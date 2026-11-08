-- Prove2me | Theorems.Thm_FRouting_eq_4
-- name    : FRouting.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:37.800693+00:00
-- url     : https://prove2.me/theorems/6ae1caee-628f-4574-b266-932b418d0368
-- title:
--   Eq. (4) — Uhlmann extension of the pure state $\Phi$
-- statement:
--   Let $\sigma$ be a density matrix on $\bar QQ_1A$, with $\bar Q,Q_1$ of dimension $d\ge2$. Then there is a density matrix $\tau_A$ with
--   $$F(\sigma_{\bar QQ_1A},\Phi_{\bar QQ_1}\otimes\tau_A)=F(\sigma_{\bar QQ_1},\Phi_{\bar QQ_1}).$$
--
--   This is the step at which the purity of $\Phi$ enters the proof of Lemma 4.2.
--
--   Differences from the source:
--   - generalization: the state σ of the proof, with F(σ_{Q̄Q₁}, Φ) ≥ 1 − ε → every density matrix σ, the equality only; reason: the inequality is the correctness hypothesis, used nowhere in the equality; the printed display follows by substituting it
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), §4.1, eq. (4), p.18

import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_FRouting_Phi
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_WildeQIT_partialTrace

set_option autoImplicit false

open scoped Kronecker

namespace FRouting

open WildeQIT

/-- **Eq. (4) (Uhlmann extension).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), §4.1, eq. (4), p.18: "Because Φ_{Q̄Q₁} is pure, Uhlmann's
theorem provides a state τ_A such that F(σ_{Q̄Q₁A}, Φ_{Q̄Q₁} ⊗ τ_A) = F(σ_{Q̄Q₁}, Φ_{Q̄Q₁}) ≥ 1 − ε."

**Formalization Note** The item is the equality, for every state `σ` on `Q̄Q₁A`; the inequality
`≥ 1 − ε` is the correctness hypothesis of the surrounding proof. `F` is the root fidelity. -/
theorem eq_4 {d : ℕ} (hd : 2 ≤ d) {A : Type} [Fintype A] [DecidableEq A]
    (σ : Matrix ((Fin d × Fin d) × A) ((Fin d × Fin d) × A) ℂ) (hσ : PeresTerno.IsDensityMatrix σ) :
    ∃ τ : Matrix A A ℂ, PeresTerno.IsDensityMatrix τ ∧
      rootFidelity σ (Phi d ⊗ₖ τ) = rootFidelity (partialTraceRight σ) (Phi d) := by sorry

end FRouting
