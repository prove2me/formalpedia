-- Prove2me | Theorems.Thm_FairKMeans_lemma_27
-- name    : FairKMeans.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:18.889115+00:00
-- url     : https://prove2.me/theorems/5b6c90b7-6bc3-4a8b-9a87-4d8391cbd2c2
-- title:
--   Lemma 27 — descent: an update decreases $\Psi$ by at least $\tfrac{\eta^2}{288}L_0$
-- statement:
--   Let $\rho\ge1$, $\varepsilon\in(0,1]$, $\eta=\min\{1/10,\varepsilon/(3\rho)\}$, $L_0\in\mathbb R$, and let $(T,\phi_T)$ be a relaxed solution with $\Psi(\phi_T)\le(1+\lambda)L_0$. Let $(\phi_{T'},z)$ be an optimal solution of LP (29) for $T'=\mathrm{WCS}_{\eta/88}(P_\lambda)$ and $V=\mathrm{WCS}_{\eta/4}(U)$, and assume that the gap $g=L(\phi_T)-L(\phi_{T'})$ exceeds $\frac{\eta}{2}L_0$. Then for $\theta=\eta/72$ the $\theta$-mixture, with candidate set $T\uplus T'$, satisfies
--
--   $$\Psi(\phi_{T_\theta})\le\Psi(\phi_T)-\frac{\eta^2}{288}L_0 .$$
--
--   This bounds the number of updates of the loop.
--
--   Differences from the source:
--   - generalization: L0 the value of line 2 of Algorithm 1 → any real L0; reason: the proof uses only Ψ(ϕT) ≤ (1+λ)L0; the algorithm's L0 is a special case
--   - encoding: (T′, ϕT′) the relaxed solution of Lemma 26 → an optimal solution (ϕT′, z) of LP (29) for the same candidate sets; reason: that is how Lemma 26 produces it
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 27, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_CandidateSets
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1

namespace FairKMeans

/-- **Lemma 27 (Descent)**, p.33 (PDF 35). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version,
sha256 73e9312c…).

Let `η = min{1/10, ε/(3ρ)}`. Suppose `Ψ(φ_T) ≤ (1+λ)L₀`, let `(T', φ_{T'})` be the relaxed
solution of Lemma 26 (from an optimal solution of LP (29) for `T' = WCS_{η/88}(P_λ)`,
`V = WCS_{η/4}(U)`), and assume the gap `g = L(φ_T) − L(φ_{T'})` is larger than `(η/2)L₀`.
Then for `θ = η/72` the θ-mixture, with candidate set `T ⊎ T'`, satisfies
`Ψ(φ_{T_θ}) ≤ Ψ(φ_T) − (η²/288)L₀`.

**Formalization Note.** `L₀` is any real number. -/
theorem lemma_27 {d n m s : ℕ} (I : Instance d n m) (ρ ε : ℝ) (hρ : 1 ≤ ρ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (L₀ : ℝ) (φ : Fin n → Fin s → ℝ) (h : IsRelaxed I φ)
    (hΨ : Psi I ρ φ ≤ (1 + lam ρ) * L₀)
    (φ' : Fin n → Fin (n ^ wcsR (eta ρ ε / 88)) → ℝ) (z : Fin (n ^ wcsR (eta ρ ε / 88)) → ℝ)
    (hopt : IsLP29Optimal I (plam I ρ φ) (uvec I ρ φ) (wcs (eta ρ ε / 88) (plam I ρ φ))
      (wcs (eta ρ ε / 4) (uvec I ρ φ)) φ' z)
    (hg : eta ρ ε / 2 * L₀ < linCost I ρ φ φ - linCost I ρ φ φ') :
    Psi I ρ (mixAssign (eta ρ ε / 72) φ φ') ≤ Psi I ρ φ - eta ρ ε ^ 2 / 288 * L₀ := by sorry

end FairKMeans
