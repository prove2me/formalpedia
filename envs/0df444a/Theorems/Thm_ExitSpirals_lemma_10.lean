-- Prove2me | Theorems.Thm_ExitSpirals_lemma_10
-- name    : ExitSpirals.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:52.149181+00:00
-- url     : https://prove2.me/theorems/2ebc909b-4056-4c76-bd5c-3a557576a724
-- title:
--   Lemma 10 (corrected: continuity needs $p^-_1<1$, C4; concavity only on $\{F>0\}$, C6) — the shape of $F(s,x)=x\,g_R(x\,g_C(s))$
-- statement:
--   Let $p_R,p_C$ be joint degree distributions with $\sum_{j,k}jk\,p_{jk}<\infty$, let $x\in[0,1]$ and $F(s,x)=x\,g_R(x\,g_C(s))$. Then, for $s\in(0,1]$:
--
--   1. if $p^-_{1,R}<1$ and $p^-_{1,C}<1$, $F(\cdot,x)$ is continuous on $(0,1]$;
--   2. $F(\cdot,x)$ is (weakly) increasing on $(0,1]$;
--   3. $F(s,x)\le x$;
--   4. if $g_R$ and $g_C$ are concave on the sets of $s\in[0,1]$ where they are positive, then $F(\cdot,x)$ is concave on $\{s\in(0,1]: F(s,x)>0\}$;
--   5. $F(s,x)\to0$ as $s\to0^+$; indeed $F(s,x)=0$ for all sufficiently small $s>0$;
--   6. $\partial F/\partial s\,(s,x)\to0$ as $s\to0^+$.
--
--   These are the facts about the shape of $F$ used to locate its fixed points: flat and zero near $0$, increasing, bounded by $x$.
--
--   **Formalization Note** The derivative in clause 6 is Mathlib's `deriv`; $F$ vanishes on an interval to the right of $0$, where it is differentiable with derivative $0$.
--
--   Differences from the source:
--   - correction: (9) and Lemma 5: g(f) = 1 − Σ_jk p_jk f^k with H built from p⁺_k = Σ_j (j/λ) p_jk (out-links) → g(s) = 1 − G(1 − s + s f(s)), G(z) = Σ_jk p_jk z^j, f the smallest root of f = H(1 − s + s f) with H built from p⁻_j = Σ_k (k/λ) p_jk (p.46); reason: the printed formula measures who can reach the giant component, but stability needs support from it: with in-degree 2 for all agents and out-degree 0 or 4 with probability ½ (Assumption 4.5 holds), every agent is active at x = 1 by Lemma 2, while the printed g gives ½ − ½f⁴ < ½
--   - correction: continuity on all of [0, 1] → continuity under the exclusion of the point mass at 1 (q_1 < 1, resp. p⁻_1 < 1); reason: for q = δ_1, H(z) = z: f(s) = 1 for s < 1 and f(1) = 0, so f, g and F jump at s = 1 (proved in the verification file)
--   - correction: clause 4: 'F(s, x) is concave in s' for s ∈ (0, 1], by Assumption 4.6 → if g_R and g_C are concave on their positivity sets, F(·, x) is concave on {s ∈ (0, 1] : F(s, x) > 0}; reason: clause 4 contradicts clauses 5–6: a function that vanishes on an interval and later becomes positive is not concave. In the (2,2)-regular case F(0.5, 1) = F(0.55, 1) = 0 and F(1, 1) = 1, below the chord at 0.55 (proved in the verification file). The page's proof uses d²g_µ/ds² < 0, i.e. concavity of g where it is positive
--   - reading: finite Σ_jk j k p_jk (needed for the critical s_c,µ of Proposition 4 that the proof uses) → hypothesis Summable (j k p_jk) for both laws; reason: the section's standing Assumption A.1(3) (Σ_i (d⁺_i)² + (d⁻_i)² = O(n)) passes to the limit law by Fatou and implies it; the page's proof invokes 'λ < ∞' for the existence of s_c,µ, which needs this moment
--   - generalization: clause 5: lim_{s→0} F(s, x) → 0 → the limit, and also F(s, x) = 0 for all small s > 0; reason: the stronger fact is what the page's proof shows ('there is a region for values of s < s_c,µ in which F is flat'); it implies the limit
--   - encoding: ∂F/∂s → Mathlib's deriv of s ↦ F(s, x); reason: F is identically 0 near 0⁺, where deriv is the classical derivative 0
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Lemma 10, p.54 and its proof, pp.54–55 (corrected)

import Mathlib
import Definitions.Def_ExitSpirals_IsDegreeDist
import Definitions.Def_ExitSpirals_giantFrac
import Definitions.Def_ExitSpirals_coupledMap

namespace ExitSpirals

open Filter Topology

/-- **Lemma 10, corrected: the shape of `F(s, x) = x g_R(x g_C(s))` on `s ∈ (0, 1]`.**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Lemma 10, p.54:
"For s ∈ (0, 1] 1. F(s, x) is continuous in s, 2. F(s, x) is monotonically increasing in s,
3. F(s, x) is bounded from above: F(s, x) ≤ x, 4. F(s, x) is concave in s, 5. lim_{s→0} F(s, x) → 0,
6. lim_{s→0} ∂F(s, x)/∂s → 0."

For joint degree distributions `p_R`, `p_C` with finite `Σ_{jk} j k p_{jk}` and `x ∈ [0, 1]`:
1. if `p⁻_{1,R} < 1` and `p⁻_{1,C} < 1`, `F(·, x)` is continuous on `(0, 1]`;
2. `F(·, x)` is monotone on `(0, 1]`;
3. `F(s, x) ≤ x` for `s ∈ (0, 1]`;
4. if `g_R` and `g_C` are concave on the sets of `s ∈ [0, 1]` where they are positive, then
   `F(·, x)` is concave on `{s ∈ (0, 1] : F(s, x) > 0}`;
5. `F(s, x) → 0` as `s → 0⁺`, and indeed `F(s, x) = 0` for all small `s > 0`;
6. `∂F/∂s(s, x) → 0` as `s → 0⁺`.

**Formalization Note.** Clause 1 needs the exclusion of the point mass `p⁻ = δ_1`, for which `g`
jumps at `s = 1`. Clause 4 as printed contradicts clause 5 (a function that vanishes on an
interval and later becomes positive is not concave); it is stated on the positivity set, from
concavity of the `g_µ`, which is what the page's proof uses. The derivative in clause 6 is
Mathlib's `deriv` (zero where `F` is not differentiable; `F` vanishes near `0⁺`). -/
theorem lemma_10 (pR pC : ℕ → ℕ → ℝ) (hpR : IsDegreeDist pR) (hpC : IsDegreeDist pC)
    (h2R : Summable fun jk : ℕ × ℕ => (jk.1 : ℝ) * jk.2 * pR jk.1 jk.2)
    (h2C : Summable fun jk : ℕ × ℕ => (jk.1 : ℝ) * jk.2 * pC jk.1 jk.2)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (edgeOriginIn pR 1 < 1 → edgeOriginIn pC 1 < 1 →
        ContinuousOn (fun s => coupledMap pR pC s x) (Set.Ioc (0 : ℝ) 1)) ∧
      MonotoneOn (fun s => coupledMap pR pC s x) (Set.Ioc (0 : ℝ) 1) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, coupledMap pR pC s x ≤ x) ∧
      (ConcaveOn ℝ {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < giantFrac pR s} (giantFrac pR) →
        ConcaveOn ℝ {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < giantFrac pC s} (giantFrac pC) →
        ConcaveOn ℝ {s : ℝ | s ∈ Set.Ioc (0 : ℝ) 1 ∧ 0 < coupledMap pR pC s x}
          (fun s => coupledMap pR pC s x)) ∧
      Tendsto (fun s => coupledMap pR pC s x) (𝓝[>] 0) (𝓝 0) ∧
      (∀ᶠ s in 𝓝[>] (0 : ℝ), coupledMap pR pC s x = 0) ∧
      Tendsto (fun s => deriv (fun t => coupledMap pR pC t x) s) (𝓝[>] 0) (𝓝 0) := by sorry

end ExitSpirals
