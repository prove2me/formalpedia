-- Prove2me | Theorems.Thm_DesignTest_swap_test_expectation
-- name    : DesignTest.swap_test_expectation
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:37.585195+00:00
-- url     : https://prove2.me/theorems/1e6e18c2-affa-4d90-be68-fc333f2d4f6b
-- title:
--   SWAP-test expectation (proof of Thm 4.11) — $\mathbb E[Z\mid\psi,\phi]=|\langle\psi|\phi\rangle|^{2t}$
-- statement:
--   Let $d\ge2$, $t\ge1$, and let $\psi,\phi$ be pure states of $\mathbb C^d$. Perform the SWAP test between $|\psi\rangle^{\otimes t}$ and $|\phi\rangle^{\otimes t}$, that is, measure $\{\Pi_+,\Pi_-\}$, $\Pi_\pm=(I\pm\mathrm{SWAP})/2$, on $\rho=(|\psi\rangle\langle\psi|)^{\otimes t}\otimes(|\phi\rangle\langle\phi|)^{\otimes t}$. Then the outcome probabilities $p_\pm=\mathrm{Tr}[\Pi_\pm\rho]$ satisfy
--   $$p_+\ge0,\qquad p_-\ge0,\qquad p_++p_-=1,\qquad p_+-p_-=|\langle\psi|\phi\rangle|^{2t}.$$
--
--   So the value $Z=+1$ on the symmetric and $Z=-1$ on the antisymmetric outcome has conditional expectation $h=|\langle\psi|\phi\rangle|^{2t}$: averaging SWAP-test values estimates the overlaps that make up the empirical frame potential.
--
--   **Formalization Note** The joint state is the Kronecker product of the two tensor powers; the probabilities are real parts of the traces. $\Pi_\pm$ are the published `QLocalCert.symProj` and `QLocalCert.antisymProj` on the register type `Fin t → Fin d`.
--
--   Differences from the source:
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: a SWAP test [BCWdW01] between |ψ_i⟩^{⊗t} and |ψ_j⟩^{⊗t} with E[Z_{ij,ℓ} | ψ] = h_ij → the projective measurement {Π₊, Π₋} on the two registers, with p₊, p₋ ≥ 0, p₊ + p₋ = 1 and p₊ − p₋ = |⟨ψ|ϕ⟩|^{2t}; reason: the Hadamard–controlled-SWAP circuit of [BCWdW01] implements exactly this measurement on the data registers; E[Z] = p₊ − p₋
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), proof of Theorem 4.11, p.38

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_empFrame
import Definitions.Def_QLocalCert_swapOp

set_option autoImplicit false

namespace DesignTest

/-- **SWAP-test expectation** (proof of Theorem 4.11). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State
and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), proof of Theorem 4.11, p.38:
`E[Z_{ij,ℓ} | ψ_1, …, ψ_{m₀}] = h_ij`.

A SWAP test between `|ψ⟩^{⊗t}` and `|ϕ⟩^{⊗t}` measures the two-outcome projective measurement
`{Π₊, Π₋}`, `Π_± = (1 ± SWAP)/2`, on `(|ψ⟩⟨ψ|)^{⊗t} ⊗ (|ϕ⟩⟨ϕ|)^{⊗t}`. Both outcome probabilities are
nonnegative and sum to `1`, and the value `+1` on the symmetric and `−1` on the antisymmetric outcome has
expectation `|⟨ψ|ϕ⟩|^{2t}`.

**Formalization Note.** The two registers are indexed by pairs of words in `Fin t → Fin d`; the joint state
is the Kronecker product of the two tensor powers. `Π₊`, `Π₋` are the published `QLocalCert.symProj` and
`QLocalCert.antisymProj` on that register type (SWAP entry `[a = b'][b = a']`). -/
theorem swap_test_expectation (d t : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t) (ψ ϕ : PureVec d) :
    let ρ := Matrix.kronecker (tensorPow ψ t) (tensorPow ϕ t)
    0 ≤ (Matrix.trace (QLocalCert.symProj (Fin t → Fin d) * ρ)).re ∧ 0 ≤ (Matrix.trace (QLocalCert.antisymProj (Fin t → Fin d) * ρ)).re ∧
      (Matrix.trace (QLocalCert.symProj (Fin t → Fin d) * ρ)).re + (Matrix.trace (QLocalCert.antisymProj (Fin t → Fin d) * ρ)).re = 1 ∧
      (Matrix.trace (QLocalCert.symProj (Fin t → Fin d) * ρ)).re - (Matrix.trace (QLocalCert.antisymProj (Fin t → Fin d) * ρ)).re =
        overlapPow t ψ ϕ := by sorry

end DesignTest
