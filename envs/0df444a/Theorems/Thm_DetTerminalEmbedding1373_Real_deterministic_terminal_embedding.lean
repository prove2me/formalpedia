-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_deterministic_terminal_embedding
-- name    : DetTerminalEmbedding1373.Real.deterministic_terminal_embedding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:46.224496+00:00
-- url     : https://prove2.me/theorems/0f111887-ae55-4880-9943-fa490b06ad68
-- title:
--   Theorem 1.1 — deterministic terminal embedding with the full dimension–time tradeoff
-- statement:
--   There are fixed deterministic preprocessing and query programs with universal numerical constants $C_{\rm pre}=C_{\rm query}=10^8$ and $C_{\rm sub}=10^{15}$. Let $X=\{x_i:i\in[n]\}\subseteq E_d$ be distinct and nonempty, let $0<\varepsilon\le1/2$, and let $2\le S\le(\varepsilon/6)^{-2}$. Put $r=\dim\operatorname{span}\{x_i-x_1\}$, $L=n\sum_{s=1}^S(2n-2)^s$, and let $D$ be the actual preprocessed memory. One map $F_D$, denoted by the fixed query program with this same state, satisfies
--
--   $$(1-\varepsilon)\|q-x_i\|\le\|F_D(q)-F_D(x_i)\|\le(1+\varepsilon)\|q-x_i\|\qquad(i\in[n],\ q\in E_d).$$
--
--   For $n\ge2$, its dimension is exactly $M=m_0+1$, where $m_0=\lceil512\log(32n(n-1))/[(\varepsilon/6)^4S]\rceil$, and
--
--   $$M\le2+\frac{4644864}{\varepsilon^4S}\log n,\quad t_{\rm pre}\le C_{\rm pre}(dn^2+MrL),$$
--
--   $$t_q\le C_{\rm query}(nd+nM\varepsilon^{-2}),\qquad t_q\le C_{\rm sub}\left(nd+\frac{n}{\varepsilon^6S}\log n\right).$$
--
--   The two displayed query envelopes are separate bounds on the same actual work $t_q$. Every preprocessing and query run halts; the output header contains the computed affine rank and dimension. No projection or runtime certificate is an input. For $n=1$, the exact map is $F(q)=\|q-x_1\|\in\mathbb R$, with preprocessing and query work bounded by the same respective constants times $d+1$, including ambient dimension zero. These finite exceptions preserve the paper's asymptotic bounds for $n\ge2$.
--
--   The result covers every admissible integer $S$ and every real query, including terminals and points outside the terminal span. Its rank-sensitive preprocessing and fixed-state semantics retain the algorithmic content of the headline theorem.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
--   - encoding: a final target dimension O(ε⁻⁴ log n/S), with projection dimension m in (38) → exact projection dimension m₀ from (38), final dimension M=m₀+1, and the explicit numerical envelope; reason: equations (40)–(41) add one coordinate; the envelope follows from log(32n(n−1))≤7 log n
--   - reading: the headline theorem uses x₁ without repeating n≥2, while Section 6 assumes n≥2 → all nonempty terminal families, with an exact singleton branch and logarithmic complexity bounds stated for n≥2; reason: the singleton radial map covers the literal finite exception; asymptotic log n bounds are not interpreted as a zero-dimensional target at n=1
--   - encoding: unit-cost real arithmetic, comparisons, square root and exponential, with O preprocessing and query bounds → fixed finite programs with all memory and integer-address operations charged, and universal constants 10⁸,10⁸,10¹⁵; reason: the constants come from the instruction and loop accounting in MODERATION_NOTES.md; no random step, log or ceiling oracle, optimizer, or uncharged query-dependent choice is used
--   - encoding: the algorithm constructs F, with r and m as quantities in the bounds → the preprocessed header additionally stores the computed affine rank r, m₀ and M, and for n=1 the map is exactly F(q)=‖q−x₁‖; reason: bookkeeping conclusions tying the charged programs to the quantities in the bounds and fixing the singleton map; they hold for the source construction and exclude no source instance
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 3–4, 20–22, Theorem 1.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_execution

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Theorem 1.1, pp. 3–4, construction in Section 6, pp. 20–22.
One fixed deterministic preprocessor/query pair; exact dimension (38) plus the
extension coordinate; the full S range; every real query; rank-sensitive work.
The singleton radial branch covers the literal nonempty statement. Complexity
bounds with log n apply for n ≥ 2, as in Section 6; singleton work is O(d+1). -/
theorem deterministic_terminal_embedding :
    ∃ Cpre Cquery Csub : ℕ,
      Cpre = 100000000 ∧ Cquery = 100000000 ∧ Csub = 1000000000000000 ∧
      Admissible preprocessingProgram ∧ Admissible queryProgram ∧
    ∀ (n d : ℕ) (hn : 0 < n) (x : Fin n → E d), Function.Injective x →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    ∀ S : ℕ, 2 ≤ S → (S : ℝ) ≤ 1 / (ε / 6) ^ 2 →
      let m := projectionDimension n ε S
      let M := targetDimension n ε S
      let input := preprocessingInput x ε S
      let tp := haltTime preprocessingProgram input
      let D := preprocess x ε S
      let F : E d → E M := embedding D M
      Halts preprocessingProgram input tp ∧
      D.ints 0 3 = (affineRank x : ℤ) ∧ D.ints 0 5 = (M : ℤ) ∧
      (∀ (i : Fin n) (q : E d),
        (1 - ε) * ‖q - x i‖ ≤ ‖F q - F (x i)‖ ∧
        ‖F q - F (x i)‖ ≤ (1 + ε) * ‖q - x i‖) ∧
      (n = 1 → M = 1 ∧ (∀ (q : E d) (j : Fin M), F q j = ‖q - baseTerminal x‖) ∧
        tp ≤ Cpre * (d + 1)) ∧
      (2 ≤ n → D.ints 0 4 = (m : ℤ) ∧ M = m + 1 ∧
        (M : ℝ) ≤ 2 + 4644864 / (ε ^ 4 * (S : ℝ)) * Real.log (n : ℝ) ∧
        tp ≤ Cpre * (d * n ^ 2 + M * affineRank x * maxTests n S)) ∧
      (∀ q : E d,
        let qi := queryInput D q
        let tq := haltTime queryProgram qi
        Halts queryProgram qi tq ∧
        (n = 1 → tq ≤ Cquery * (d + 1)) ∧
        (2 ≤ n →
          (tq : ℝ) ≤ (Cquery : ℝ) *
            ((n : ℝ) * (d : ℝ) + (n : ℝ) * (M : ℝ) / ε ^ 2) ∧
          (tq : ℝ) ≤ (Csub : ℝ) *
            ((n : ℝ) * (d : ℝ) + (n : ℝ) / (ε ^ 6 * (S : ℝ)) * Real.log (n : ℝ)))) := by sorry

end DetTerminalEmbedding1373.Real
