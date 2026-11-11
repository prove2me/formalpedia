-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_4_8
-- name    : CosetTreeSVP.SVP.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:34:59.331221+00:00
-- url     : https://prove2.me/theorems/0ef873f2-539d-4894-aecf-bf0f0a945b0e
-- title:
--   Lemma 4.8 — Algorithm 1: except with probability o(1) over δ, all Â_δ(θ), θ ∈ H_m, are computed in time and space 2^{n/2+o(n)}
-- statement:
--   Let $p, q, m, Q, N$ be the parameters of Eq. (17) and §4.3 and $\hat A_\delta$ the estimator of Eq. (33).
--
--   **Lemma 4.8.** There are a program $P$ of the randomized rational RAM, a function $g$ with $g(n)/n \to 0$, $K \in \mathbb N$, $\varepsilon(n) \to 0$ and $n_0$ such that for all $n \ge n_0$, every nonsingular $B \in \mathbb Q^{n\times n}$, every $U \in GL_n(\mathbb F_q)$ and all samples $X_{r,i} = B^{-T}z_{r,i} \in L^*$ ($z_{r,i} \in \mathbb Z^n$), except with probability at most $\varepsilon(n)$ over $\delta$: on every coin tape, $P$ on input $(B, U, (z_{r,i}), \delta)$ halts with a list of all $\theta \in H_m$, each once, with rational vectors $c_{\theta,0},\dots,c_{\theta,q-1}$ such that
--   $$\hat A_\delta(\theta) = 2\pi i\sum_{k=0}^{q-1}\omega_q^k\,c_{\theta,k},$$
--   within bit time and bit space $2^{n/2+g(n)}(\ell_B+\ell_X+1)^K$, where $\ell_B$ is the bit length of $B$ and $\ell_X$ the largest bit length of one sample.
--
--   Batch computation over all $\theta$ is what keeps the search over $H_m$ within $2^{n/2+o(n)}$.
--
--   Differences from the source:
--   - encoding: o(1) over δ and 2^{n/2+o(n)} → ε(n) → 0, g with g(n)/n → 0, n₀, chosen before n, B, U and the samples; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - reading: 'can be computed in time and space 2^{n/2+o(n)}' (polynomial factors in the bit length of the inputs, p. 11) → one program P of TwMSOCount.Main, on every coin tape, bit time and bit space ≤ 2^{n/2+g(n)}(ℓ_B + ℓ_X + 1)^K with ℓ_X the bit length of one sample; reason: the input holds pN = 2^{n/2+o(n)} samples, so a polynomial in the total input length would allow 2^{Kn/2}; the polynomial factor is in the bit length of each input item
--   - encoding: 'all vectors Â_δ(θ) … computed' (exact arithmetic, p. 11) → exact output: for each θ ∈ H_m, rational vectors c_{θ,k} with Â_δ(θ) = 2πi Σ_k ω_q^k c_{θ,k}; reason: Â_δ(θ)/(2πi) lies in ℚ(ω_q)ⁿ for a rational basis
--   - encoding: samples X_{r,i} ∈ L* → integer coordinate vectors z_{r,i} with X_{r,i} = B^{−T}z_{r,i}; reason: L* = B^{−T}ℤⁿ
--   - encoding: p, q, m, N of Eq. (17) (undefined while n/log³ n < 1) → pN n = 2^{⌊log₂ ⌊n/ln³ n⌋⌋}, qN n = least prime > 2√p, mN n = log₂ p + 1, QN n = q^{⌊n/m⌋}, NN n = Q p⁴; statements for n ≥ n₀; reason: Eq. (17) literally; for small n the values are placeholders and n₀ is quantified with the other constants
--   - generalization: m = log₂ p + 1 is assumed to divide n, and H_j is the j-th block of n/m coordinates (p. 16) → every n ≥ n₀, with footnote 7's blocks: blocks 1, …, m−1 of ℓ = ⌊n/m⌋ coordinates and block m of the remaining n − (m−1)ℓ; Q = q^ℓ; reason: footnote 7 gives this decomposition for all n; when m | n it is exactly the main text's, so the Lean statement specializes to the printed one
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 20 (PDF 22), Lemma 4.8

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_SolvesSVPWithin
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics
import Definitions.Def_CosetTreeSVP_SVP_Tree
import Definitions.Def_CosetTreeSVP_SVP_Algo

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_4_8 :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ) (ε : ℕ → ℝ),
      Tendsto (fun n => g n / n) atTop (𝓝 0) ∧ Tendsto ε atTop (𝓝 0) ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
      ∀ (U : Matrix.GeneralLinearGroup (Fin n) (ZMod (qN n)))
        (z : Fin (pN n) → Fin (NN n) → Fin n → ℤ),
        prDelta (p := pN n) (m := mN n)
          {δ | ¬ ∀ τ : ℕ → Bool, ∃ s : RunStats,
              runStats P τ (Config.init (encAlg1 B U z δ)) = some s ∧
              AhatOutputOK (QN n) B U z δ s.final.output ∧
              (s.time : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 + g n) *
                ((SuperlatSVP.inputBits B : ℝ) + sampleBits z + 1) ^ K ∧
              (s.space : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 + g n) *
                ((SuperlatSVP.inputBits B : ℝ) + sampleBits z + 1) ^ K} ≤
          ENNReal.ofReal (ε n) := by sorry

end CosetTreeSVP.SVP
