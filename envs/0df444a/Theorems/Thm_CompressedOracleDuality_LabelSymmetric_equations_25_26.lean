-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equations_25_26
-- name    : CompressedOracleDuality.LabelSymmetric.equations_25_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:03:29.523608+00:00
-- url     : https://prove2.me/theorems/b3f679a2-0a3c-4974-9625-441bcd3174f7
-- title:
--   Equations (25)–(26) — square-root POVM and the exact joint law
-- statement:
--   Let $B$ be a coefficient matrix of a normalized joint memory–database state: $\operatorname{Tr}(B^\dagger B)=1$. Put $G=B^\dagger B$, $\rho=BB^\dagger$ and $U=\rho^{-1/2}B$, with inverse zero on the kernel. Then $B=U\sqrt G$, $U$ is a partial isometry ($UU^\dagger U=U$) with $\ker U=\ker B$, and $U^\dagger B=\sqrt G$. The effects $E_D=U|D\rangle\langle D|U^\dagger$, together with $E_\bot=I-UU^\dagger$, form a POVM. They satisfy
--   $$E_D=\rho^{-1/2}(B|D\rangle\langle D|B^\dagger)\rho^{-1/2},\qquad\langle D|B^\dagger E_{\widetilde D}B|D\rangle=|(\sqrt G)_{\widetilde D,D}|^2.$$
--   The failure effect has zero joint weight for every ensemble label. The displayed effects are exactly the square-root measurement of the ensemble of conditional memory states with weights $G_{D,D}$, including zero-weight columns. This identifies the joint database law with an actual measurement on memory.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ with n-bit input and label registers → Fin (2^n) inputs and Qubits n labels; reason: these bases are bijective; addition on labels is bitwise XOR
--   - generalization: standing N ≥ 64 → all n ≥ 0 in this algebraic or information statement; reason: the finite matrix identity and measurement bound do not use the lower bound on N and include every source instance
--   - encoding: weighted normalized conditional states p_D and ψ^D → unnormalized column densities b_D b_D†; reason: their product equals p_D times the pure density, and zero columns need no arbitrary normalized state
--   - generalization: the memory is the algorithm register of dimension 2^S → any finite memory coordinate basis; reason: the polar and measurement identities hold on any finite-dimensional space and specialize to the source memory basis
--   - encoding: U is the unique partial isometry with A = U√G and ker U = ker A (p. 14) → U is the constructed ρ^{-1/2}B, and the theorem states A = U√G, UU†U = U and ker U = ker B; reason: these three properties characterize the polar factor, so it is the same operator and the first equality of (25) keeps its content
--   - encoding: ⟨D|A†E A|D⟩ as a probability → real part of the diagonal entry; reason: E is positive semidefinite, so the entry is real
--   - generalization: (26) gives the law of the database outcomes → also states that E_⊥ has zero weight for every ensemble label; reason: an added conclusion, since the database outcomes already exhaust p_D by (24); dropping it leaves the source claim
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 15, (25)–(26)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Measurement

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- (25)–(26), p.15: canonical polar factor, completed square-root POVM and joint law. -/
theorem equations_25_26 {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι (Database n) ℂ) (hnorm : (B.conjTranspose * B).trace = 1) :
    B = polarFactor B * sqrtGram (B.conjTranspose * B) ∧
    polarFactor B * (polarFactor B).conjTranspose * polarFactor B = polarFactor B ∧
    (∀ v : Database n → ℂ, (polarFactor B).mulVec v = 0 ↔ B.mulVec v = 0) ∧
    (polarFactor B).conjTranspose * B = sqrtGram (B.conjTranspose * B) ∧
    IsPOVM (dualPOVM B) ∧
    (∀ D, dualPOVM B (some D) =
      inverseSqrt (B * B.conjTranspose) * columnDensity B D * inverseSqrt (B * B.conjTranspose)) ∧
    (∀ Dₜ D, ((B.conjTranspose * dualPOVM B (some Dₜ) * B) D D).re =
      jointLaw (B.conjTranspose * B) (Dₜ, D)) ∧
    (∀ D, ((B.conjTranspose * dualPOVM B none * B) D D).re = 0) := by sorry

end CompressedOracleDuality.LabelSymmetric
