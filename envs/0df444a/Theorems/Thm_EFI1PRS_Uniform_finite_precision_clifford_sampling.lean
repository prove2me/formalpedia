-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_finite_precision_clifford_sampling
-- name    : EFI1PRS.Uniform.finite_precision_clifford_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:02:46.431637+00:00
-- url     : https://prove2.me/theorems/1571e5f1-bc52-4ec5-ad64-415b1ec5927a
-- title:
--   Lemma 2.17 — finite-precision Clifford sampling
-- statement:
--   For the entire $t$-qubit Clifford group modulo global phase, set
--
--   $$K_t=2^{t^2+2t}\prod_{j=1}^t(4^j-1),\qquad a=\lceil\log_2K_t\rceil+\lambda^2.$$
--
--   The explicit modulo-and-indexing map from uniform $a$-bit seeds produces exact Clifford circuits in polynomial time. The phase quotient has $K_t$ elements and the circuit distribution is within $2^{-\lambda^2}$ of uniform in total variation. Moreover, for every normalized state with arbitrary quantum side information, if uniform Clifford extraction has error at most $\varepsilon$, then
--
--   $$D(\text{raw-seed extraction},\text{independent uniform raw seed and ideal state})\le\varepsilon+2^{-\lambda^2}.$$
--
--   The seed bits themselves remain exactly uniform and are publicly included. The efficient synthesis claim refers to actual finite gate descriptions, not to unit-cost dense matrices.
--
--   Differences from the source:
--   - encoding: efficient Clifford indexing and synthesis from the cited algorithm → explicit Figure 2 symplectic transvections lifted by Pauli-to-Z conjugation to H/S/CNOT circuits; reason: this specifies a concrete exact synthesis map and leaves its quotient correspondence, complexity and error as theorem conclusions
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Lemma 2.17, PDF/printed p. 10

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_precision_clifford_sampling :
    (∃ enumerations : (m : ℕ) → Fintype (QAlgorithms.Clifford.ProjectiveGroup m),
      ∀ m, @Fintype.card (QAlgorithms.Clifford.ProjectiveGroup m) (enumerations m) = cliffordCount m) ∧
    (∃ machine : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable machine ∧
      ∀ m sec, 1 ≤ sec → ∀ s : Qubits (seedLength m sec),
        machine (QAlgorithms.Complexity.encNat m ++ QAlgorithms.Complexity.encNat sec ++ List.ofFn s) =
          samplerCode m sec s) ∧
    (∀ m sec, 1 ≤ sec → ∀ s : Qubits (seedLength m sec),
      IsExactClifford m (sampledCircuit m sec s).unitary) ∧
    (∀ (m : ℕ) (enumeration : Fintype (QAlgorithms.Clifford.ProjectiveGroup m)),
      letI := enumeration
      ∀ sec, 1 ≤ sec → (1/2 : ℝ) *
        ∑ U : QAlgorithms.Clifford.ProjectiveGroup m,
          |samplerProbability m sec U - (Fintype.card (QAlgorithms.Clifford.ProjectiveGroup m) : ℝ)⁻¹| ≤
            (2 : ℝ)^(-((sec^2 : ℕ) : ℤ))) ∧
    (∀ (m ell sec : ℕ), ell ≤ m → 1 ≤ sec →
      ∀ (enumeration : Fintype (QAlgorithms.Clifford.ProjectiveGroup m)),
      letI := enumeration
      ∀ (B : Type) [Fintype B] [Nonempty B]
        (ζ : Matrix (Qubits m × B) (Qubits m × B) ℂ), IsDensityMatrix ζ → ∀ ε : ℝ,
        ((∑ U : QAlgorithms.Clifford.ProjectiveGroup m,
          distance (extractColumn m ell (cliffordMatrix U) ζ) (idealExtracted m ell ζ)) /
          (Fintype.card (QAlgorithms.Clifford.ProjectiveGroup m) : ℝ) ≤ ε) →
        distance (seededExtraction m ell sec ζ) (seededIdeal m ell sec ζ) ≤
          ε + (2 : ℝ)^(-((sec^2 : ℕ) : ℤ))) := by sorry

end EFI1PRS.Uniform
