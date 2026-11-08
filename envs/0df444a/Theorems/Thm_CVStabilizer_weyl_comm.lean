-- Prove2me | Theorems.Thm_CVStabilizer_weyl_comm
-- name    : CVStabilizer.weyl_comm
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:20:59.111545+00:00
-- url     : https://prove2.me/theorems/301a9941-a495-40d4-bd7a-8036fc934233
-- title:
--   Eq. (3): $U(v)U(v')=e^{i\pi\omega(v,v')}U(v')U(v)$
-- statement:
--   For all $v,v'\in\mathbb R^{2n}$, any two Weyl operators commute up to a phase given by the standard symplectic form:
--
--   $$
--   U(v)\,U(v')=e^{i\pi\omega(v,v')}\,U(v')\,U(v),\qquad \omega(v,v')=\sum_{i=1}^n(s_it'_i-s'_it_i).
--   $$
--
--   In particular $U(v)$ and $U(v')$ commute when $\omega(v,v')=0$, which is how abelian stabilizers are built from symplectically orthogonal vectors.
--
--   **Formalization Note** $U$ is the concrete realization $(U(s,t)\psi)(x)=e^{i\pi(\langle t,x\rangle+\langle s,t\rangle/2)}\psi(x+s)$ acting on all functions $\mathbb R^n\to\mathbb C$; operators are composed with $\circ$ and a scalar $c$ acts as $\psi\mapsto c\,\psi$.
--
--   Differences from the source:
--   - reading: U(v) = exp(iπ Σᵢ (sᵢp̂ᵢ + tᵢq̂ᵢ)) with [q̂, p̂] = 1 (2), which under no normalization of the canonical pair yields (3) as printed → the concrete realization weyl: (U(s,t)ψ)(x) = e^{iπ(⟨t,x⟩ + ⟨s,t⟩/2)} ψ(x + s); reason: (3), (7) and every example of the paper use (3); in this realization (3) and (7) hold verbatim, Z(t) = U(0,t) is the multiplication by e^{iπtx} of (11), X(s) = U(s,0) is the position shift ψ ↦ ψ(· + s), i.e. X(s)|q⟩ = |q − s⟩ (this direction is forced by (3) once Z(t) is the multiplication of (11); the p.3 example X̄(q)|000⟩ = |qqq⟩ reads the shift the other way, which is the paper's inconsistency, and no item depends on it), and the symmetric phase e^{iπ⟨s,t⟩/2} gives U(av)U(bv) = U((a+b)v)
--   - generalization: operators on the state space with position basis |q⟩ → operators on all functions ℝⁿ → ℂ; identities hold pointwise; reason: the position eigenvectors |q⟩ are not in L²; each U(v) is a shift followed by multiplication by a continuous phase, so it preserves L² and a.e. equality, every operator identity restricts to L²(ℝⁿ), and equality, commutation and injectivity of the U(v) are the same on L² as on all functions
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, eq. (3), p.1

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **The commutation relation (3)**, Barnes, arXiv:quant-ph/0405064v1, p.1: "with any two
operators commuting up to a phase: U(v)U(v′) = e^{iπω(v,v′)}U(v′)U(v), (3) where
ω(v, v′) = Σᵢ₌₁ⁿ(sᵢt′ᵢ − s′ᵢtᵢ) is the standard symplectic form on ℝ²ⁿ."

**Formalization Note** `U` is the concrete realization `weyl`, in which (3) holds as printed. -/
theorem weyl_comm (n : ℕ) (v v' : PhaseSpace n) :
    weyl v ∘ weyl v' =
      (fun ψ => Complex.exp (((Real.pi * omega n v v' : ℝ) : ℂ) * Complex.I) • ψ)
        ∘ weyl v' ∘ weyl v := by sorry

end CVStabilizer
