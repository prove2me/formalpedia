-- Prove2me | Theorems.Thm_FairKMeans_lemma_25
-- name    : FairKMeans.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:08.750056+00:00
-- url     : https://prove2.me/theorems/1f3ba56a-b3e2-46ec-9a22-eae48e13eef9
-- title:
--   Lemma 25 — bounded iterates: $C_\nu\le L_0$, $L(\phi_T)\le 3L_0$, and $L(\phi_{T'})\le\tfrac{16}{5}L_0\Rightarrow C_{T'}\le 10L_0$
-- statement:
--   Let $\rho\ge1$, $\lambda=\rho/(1+\rho)$, $L_0\in\mathbb R$, and let $(T,\phi_T)$ be a relaxed solution with $\Psi(\phi_T)\le(1+\lambda)L_0$; let $L$ be the linearized cost at $(T,\phi_T)$. Then
--
--   1. $C_\nu\le L_0$, and $L(\phi_T)=C_T+2\lambda C_\nu\le 3L_0$;
--   2. $L(\phi_{T'})\ge C_{T'}-2\sqrt{L_0\,C_{T'}}$ for every relaxed solution $(T',\phi_{T'})$;
--   3. if a relaxed solution satisfies $L(\phi_{T'})\le\frac{16}{5}L_0$, then $C_{T'}\le 10L_0$.
--
--   These bounds keep the candidate sets of every iteration accurate enough.
--
--   Differences from the source:
--   - generalization: L0 the value of line 2 of Algorithm 1 → any real L0; reason: the proof uses only Ψ(ϕT) ≤ (1+λ)L0; the algorithm's L0 is a special case
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 25, items 1–3, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_RelaxedSolution

namespace FairKMeans

/-- **Lemma 25 (Bounded iterates)**, p.31 (PDF 33). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held
version, sha256 73e9312c…).

Suppose the relaxed solution `(T, φ_T)` satisfies `Ψ(φ_T) ≤ (1+λ)L₀`, and let `L` be the
linearized cost at `(T, φ_T)`. Then
1. `C_ν ≤ L₀`, and `L(φ_T) = C_T + 2λC_ν ≤ 3L₀`;
2. `L(φ_{T'}) ≥ C_{T'} − 2√(L₀ C_{T'})` for every relaxed solution `(T', φ_{T'})`;
3. if a relaxed solution satisfies `L(φ_{T'}) ≤ (16/5)L₀`, then `C_{T'} ≤ 10L₀`.

**Formalization Note.** `L₀` is any real number (in the paper, the value of line 2 of
Algorithm 1). -/
theorem lemma_25 {d n m s : ℕ} (I : Instance d n m) (ρ : ℝ) (hρ : 1 ≤ ρ) (L₀ : ℝ)
    (φ : Fin n → Fin s → ℝ) (h : IsRelaxed I φ) (hΨ : Psi I ρ φ ≤ (1 + lam ρ) * L₀) :
    (Cnu I φ ≤ L₀ ∧ linCost I ρ φ φ = CT I φ + 2 * lam ρ * Cnu I φ ∧
        linCost I ρ φ φ ≤ 3 * L₀) ∧
      (∀ (s' : ℕ) (φ' : Fin n → Fin s' → ℝ), IsRelaxed I φ' →
        CT I φ' - 2 * Real.sqrt (L₀ * CT I φ') ≤ linCost I ρ φ φ') ∧
      (∀ (s' : ℕ) (φ' : Fin n → Fin s' → ℝ), IsRelaxed I φ' →
        linCost I ρ φ φ' ≤ 16 / 5 * L₀ → CT I φ' ≤ 10 * L₀) := by sorry

end FairKMeans
