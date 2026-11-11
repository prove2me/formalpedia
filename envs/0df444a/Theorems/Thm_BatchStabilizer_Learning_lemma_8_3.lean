-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_8_3
-- name    : BatchStabilizer.Learning.lemma_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:56.627551+00:00
-- url     : https://prove2.me/theorems/375f8bcb-0c97-47f1-9c05-eb53f2b5b7ab
-- title:
--   Lemma 8.3 — recovery of the target stabilizer signs
-- statement:
--   Let $\rho$ be a density matrix with $F(\rho)\ge\tau>0$, $P=|\phi^*\rangle\langle\phi^*|$ the fixed optimal target with label space $T$, and $0<\delta<1$. Let $\mathcal L_{\rm cert}$ be a list of full isotropic spaces containing $T$ and $\mathcal R$ a list of full isotropic representatives such that every $T'\in\mathcal L_{\rm cert}$ has some $T_i\in\mathcal R$ with $\dim(T'\cap T_i)\ge n-t$. Then, with probability at least $1-\delta/8$ over the fresh representative-basis measurements ($m_6$ per representative), Algorithm 4 outputs a signed candidate list $\mathcal C$ containing $|\phi^*\rangle$; and on every transcript
--   $$|\mathcal C|\le|\mathcal L_{\rm cert}|\,m_6\,2^t .$$
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: the label space T of a fixed optimal stabilizer state |ϕ*⟩ → labelSpace P for a projector P with IsOptimalStab ρ P (P ∈ Stab_n and tr(ρP) = F(ρ)); reason: states are compared as projectors; the span of the stabilizing labels of a stabilizer projector is its label space
--   - generalization: 0 < τ ≤ 1/2 with F(ρ) ≥ τ (the range of Theorem 1.1) → any τ > 0 with τ ≤ F(ρ); reason: a larger parameter range; it specializes to the source's range
--   - generalization: 0 < δ < 1/3 (the range of Theorem 1.1, in force throughout §§7–9) → 0 < δ < 1; reason: a larger parameter range; it specializes to the source's range
--   - generalization: conditional on the earlier measurement batches (the lists produced by the previous stages) → every fixed list (or set) satisfying the stated hypotheses, with probability over the fresh independent batch only; reason: conditioning on the earlier batches fixes these inputs; a statement for every fixed input specializes to the conditional one
--   - encoding: the signed stabilizer states consistent with the observed signs on J = T' ∩ T_i → signed projectors ∏(I + (−1)^{c_j}W_{b_j})/2 on a fixed basis of T' whose eigenvalue on every W_t, t ∈ J, matches that of the observed outcome sector; reason: this is the consistency condition the source's tableau enumeration computes
--   - generalization: a representative set ℛ ⊆ ℒ_cert with the covering guarantee of Lemma 8.2 → any list ℛ of full isotropic spaces (not required to lie in ℒ_cert or to satisfy |ℛ| ≤ 4/τ²) such that every T' ∈ ℒ_cert has some T_i ∈ ℛ with dim(T' ∩ T_i) ≥ n − t, n − t in ℤ; T' is assigned to the first such T_i; reason: the proof uses only the covering property and that each T_i is a full stabilizer basis; ℛ from Lemma 8.2 is such a list
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 35–36 (PDF p. 36–37), Lemma 8.3, equation (104)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 8.3, printed pp. 35–36 (PDF pp. 36–37): if `T ∈ ℒ_cert` and the representatives cover
`ℒ_cert` as in Lemma 8.2, then with probability at least `1 - δ/8` over the fresh
representative-basis measurements Algorithm 4 outputs a signed list containing the fixed
optimal target `|ϕ*⟩`; on every transcript, `|𝒞| ≤ |ℒ_cert| m₆ 2^t` (104). -/
theorem lemma_8_3 {n : ℕ} (ρ P : Op (Qubits n)) (hρ : IsDensity ρ) (hP : IsOptimalStab ρ P)
    (τ δ : ℝ) (hτ : 0 < τ) (hF : τ ≤ stabFidelity ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (cert reps : List (Sub n)) (hfull : ∀ T' ∈ cert, IsFull T') (hreps : ∀ Ti ∈ reps, IsFull Ti)
    (hT : labelSpace P ∈ cert)
    (hcover : ∀ T' ∈ cert, ∃ Ti ∈ reps,
      (n : ℤ) - tt τ ≤ (Module.finrank (ZMod 2) ↥(T' ⊓ Ti) : ℤ)) :
    1 - δ / 8 ≤ (alg4Prog n τ δ cert reps).prob ρ (fun Cs => P ∈ Cs) ∧
      (alg4Prog n τ δ cert reps).allRuns
        (fun _ Cs => Cs.length ≤ cert.length * m6 τ δ * 2 ^ tt τ) := by sorry

end BatchStabilizer.Learning
