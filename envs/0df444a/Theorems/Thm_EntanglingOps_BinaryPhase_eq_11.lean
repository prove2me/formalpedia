-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_eq_11
-- name    : EntanglingOps.BinaryPhase.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:24.930994+00:00
-- url     : https://prove2.me/theorems/08ae8679-85d6-4024-b6ac-827d7fc85ca2
-- title:
--   Eq. (11), p. 3 — E(ψ_α) = h(cos² α) in bits; E(ψ_{α₂}) = 1, E(ψ_{α₁}) = 0, U(π/2) = −iσ_x ⊗ σ_x
-- statement:
--   Let $E(\psi)$ be the entropy of entanglement of a pure state $\psi$ of $A_1A_2B_1B_2$ across $(A_1A_2)|(B_1B_2)$: the von Neumann entropy, with logarithms to base 2, of $\operatorname{tr}_{B_1B_2}|\psi\rangle\langle\psi|$. Let $h(x)=-x\log_2x-(1-x)\log_2(1-x)$. Then:
--
--   1. for every real $\alpha$, with $x=\cos^2\alpha$,
--   $$E(\psi_\alpha)=-x\log_2(x)-(1-x)\log_2(1-x);$$
--   in particular $E(\psi_{\alpha_N})=h(\cos^2(\pi/2^N))$;
--   2. $E(\psi_{\alpha_2})=1$;
--   3. $E(\psi_{\alpha_1})=0$;
--   4. $U(\pi/2)=-i\,\sigma_x\otimes\sigma_x$.
--
--   Items 2–4 are the two ends of the family: $U(\pi/4)$ needs one ebit, while $U(\pi/2)$ is a product of one-qubit operators, a local gate.
--
--   Differences from the source:
--   - generalization: x = cos²(α_N) → every real α; reason: α = α_N is an instance
--   - encoding: entropy of entanglement → von Neumann entropy (QAlgorithms.vnEntropy, base 2) of the A1A2 marginal partialTraceRight |ψ⟩⟨ψ|; reason: the standard definition for pure states; bits as in (11)
--   - reading: 'U(π/4) is capable of creating 1 ebit', 'U(π/2) is a local gate' → the equalities E(ψ_{α₂}) = 1 and U(π/2) = (−i)·(σ_x ⊗ σ_x); reason: the interpretive clauses are carried by these equalities; −iσ_x ⊗ σ_x is a product of one-qubit operators
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 3, Eq. (11) and the two sentences after it

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- Eq. (11), p. 3: the entropy of entanglement (bits) of `|ψ_α⟩` across `(A₁A₂)|(B₁B₂)` is the
binary entropy of `x = cos² α`; `E(ψ_{α₂}) = 1`, `E(ψ_{α₁}) = 0`; and
`U(π/2) = −i σ_x ⊗ σ_x`. The first identity is stated for every real `α`. -/
theorem eq_11 :
    (∀ α : ℝ, entEntropy (resource α) = WildeQIT.binaryEntropy (Real.cos α ^ 2)) ∧
    entEntropy (resource (alphaN 2)) = 1 ∧
    entEntropy (resource (alphaN 1)) = 0 ∧
    gate (Real.pi / 2) = (-Complex.I) • (sx ⊗ₖ sx) := by sorry

end EntanglingOps.BinaryPhase
