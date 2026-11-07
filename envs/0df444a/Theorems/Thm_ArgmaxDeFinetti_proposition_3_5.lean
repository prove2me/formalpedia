-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_proposition_3_5
-- name    : ArgmaxDeFinetti.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:57.90822+00:00
-- url     : https://prove2.me/theorems/49ec2968-5aa0-49c7-a4b5-9b8dd78f1df3
-- title:
--   Proposition 3.5 — integrality gap from argmax rounding
-- statement:
--   For every $N,d\ge2$ and every $M\in\mathrm{Herm}(\mathrm{Sym}^2(\mathbb C^d))$,
--   $$
--   \lambda_{\max}(M^{[N]})-h(M)\le\frac{\tau(M)}{N-1},
--   $$
--   and consequently
--   $$
--   \lambda_{\max}(M^{[N]})-h(M)\le\frac{\sqrt{d-1}}{N-1}\,\|M\|_\infty .
--   $$
--   Here $\lambda_{\max}(M^{[N]})$ is the top eigenvalue of the normalized lift on $\mathrm{Sym}^N$, $h(M)$ the maximum of $\langle u^{\otimes2}|M|u^{\otimes2}\rangle$ over unit $u$, and $\tau(M)=\sup_{\|u\|=1}\|P_{\mathrm{Sym}^2(u^\perp)}Mu^{\otimes2}\|_\pi$. Inserted into Lemma 3.2, the second bound gives Theorem 3.1.
--
--   Differences from the source:
--   - encoding: M ∈ Herm(Sym²(H)) → a Hermitian matrix on ℂ^d ⊗ ℂ^d with U_π M = M U_π = M for π ∈ S₂ (IsSymWitness); reason: extension by zero of the operator on Sym²; it has the same operator norm, a_M, h(M), lift and τ(M)
--   - encoding: λ_max(M^[N]) of M^[N] on Sym^N(H) → supremum of Re⟨ψ, M^[N]ψ⟩ over unit ψ ∈ Sym^N (lamMaxSym); reason: the top eigenvalue of a Hermitian operator on Sym^N is its largest Rayleigh quotient
--   - encoding: ∥P_{Sym²(u⊥)} M u^⊗2∥_π, projective norm across the two copies of u⊥ → projNorm on ℂ^d ⊗ ℂ^d of (P_{u⊥} ⊗ P_{u⊥}) M u^⊗2 (tau); reason: M u^⊗2 ∈ Sym², where P_{Sym²(u⊥)} = P_{u⊥} ⊗ P_{u⊥}, and for a vector of u⊥ ⊗ u⊥ both projective norms equal the trace norm of its coefficient matrix (2.15)
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Proposition 3.5, p.26, eqs. (3.17)–(3.18)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_opNormS
import Definitions.Def_ArgmaxDeFinetti_IsSymWitness
import Definitions.Def_ArgmaxDeFinetti_hM
import Definitions.Def_ArgmaxDeFinetti_lamMaxSym
import Definitions.Def_ArgmaxDeFinetti_tau

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Proposition 3.5 (Integrality gap from argmax rounding)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.26, eqs. (3.17)–(3.18). For every
`N, d ≥ 2` and every `M ∈ Herm(Sym²(ℂ^d))`, `λ_max(M^{[N]}) − h(M) ≤ τ(M)/(N − 1)` (3.17), and consequently
`λ_max(M^{[N]}) − h(M) ≤ √(d − 1)/(N − 1) · ∥M∥_∞` (3.18).

**Formalization Note** `M ∈ Herm(Sym²)` is `IsSymWitness M`; `λ_max` on `Sym^N` is `lamMaxSym`; `τ` is (3.16);
`∥M∥_∞` is `opNormS`. No bound on `∥M∥_∞` is assumed. -/
theorem proposition_3_5 (N d : ℕ) (hN : 2 ≤ N) (hd : 2 ≤ d) (M : Op 2 d) (hMw : IsSymWitness M) :
    lamMaxSym N M - hM M ≤ tau M / ((N : ℝ) - 1) ∧
    lamMaxSym N M - hM M ≤ Real.sqrt ((d : ℝ) - 1) / ((N : ℝ) - 1) * opNormS M := by sorry

end ArgmaxDeFinetti
