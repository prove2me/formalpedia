-- Prove2me | Theorems.Thm_CVStabilizer_weyl_mul
-- name    : CVStabilizer.weyl_mul
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:20:59.81071+00:00
-- url     : https://prove2.me/theorems/17ed17ef-c3d9-42ca-b8fb-12910ed6a654
-- title:
--   Weyl product law: $U(v)U(v')=e^{i\pi\omega(v,v')/2}U(v+v')$ and real powers
-- statement:
--   For all $v,v'\in\mathbb R^{2n}$ and all real $a,b$,
--
--   $$
--   U(v)\,U(v')=e^{i\pi\omega(v,v')/2}\,U(v+v'),\qquad U(av)\,U(bv)=U((a+b)v).
--   $$
--
--   This makes precise the correspondence of p.1: multiplication of Pauli operators corresponds to addition of vectors up to a phase, and scaling a vector by a real number corresponds to a real power of the operator. It is the group law from which the commutation relation (3) and all later identities follow.
--
--   **Formalization Note** $U$ is the concrete realization $(U(s,t)\psi)(x)=e^{i\pi(\langle t,x\rangle+\langle s,t\rangle/2)}\psi(x+s)$ acting on all functions $\mathbb R^n\to\mathbb C$; operators are composed with $\circ$ and a scalar $c$ acts as $\psi\mapsto c\,\psi$.
--
--   Differences from the source:
--   - reading: U(v) = exp(iπ Σᵢ (sᵢp̂ᵢ + tᵢq̂ᵢ)) with [q̂, p̂] = 1 (2), which under no normalization of the canonical pair yields (3) as printed → the concrete realization weyl: (U(s,t)ψ)(x) = e^{iπ(⟨t,x⟩ + ⟨s,t⟩/2)} ψ(x + s); reason: (3), (7) and every example of the paper use (3); in this realization (3) and (7) hold verbatim, Z(t) = U(0,t) is the multiplication by e^{iπtx} of (11), X(s) = U(s,0) is the position shift ψ ↦ ψ(· + s), i.e. X(s)|q⟩ = |q − s⟩ (this direction is forced by (3) once Z(t) is the multiplication of (11); the p.3 example X̄(q)|000⟩ = |qqq⟩ reads the shift the other way, which is the paper's inconsistency, and no item depends on it), and the symmetric phase e^{iπ⟨s,t⟩/2} gives U(av)U(bv) = U((a+b)v)
--   - generalization: operators on the state space with position basis |q⟩ → operators on all functions ℝⁿ → ℂ; identities hold pointwise; reason: the position eigenvectors |q⟩ are not in L²; each U(v) is a shift followed by multiplication by a continuous phase, so it preserves L² and a.e. equality, every operator identity restricts to L²(ℝⁿ), and equality, commutation and injectivity of the U(v) are the same on L² as on all functions
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, p.1, right column, after (3) ("This gives us an immediate correspondence between Gn and the symplectic vector space R2n…")

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **Weyl product law**, Barnes, arXiv:quant-ph/0405064v1, p.1, right column, after (3): "The
operator U(v) corresponds to the vector v, multiplication of operators corresponds to addition of
vectors (up to phase), and scaling of vectors by real numbers corresponds to taking real-number
powers of operators." Precisely: `U(v)U(v′) = e^{iπω(v,v′)/2} U(v + v′)` for all `v, v′`, and
`U(av)U(bv) = U((a + b)v)` for all real `a, b`.

**Formalization Note** `U` is the concrete realization `weyl` (see its docstring); the phase
`e^{iπω(v,v′)/2}` is the "up to phase" of the page. Operators on functions `ℝⁿ → ℂ` are composed
with `∘`; a scalar `c` acts as `ψ ↦ c • ψ`. -/
theorem weyl_mul (n : ℕ) :
    (∀ v v' : PhaseSpace n, weyl v ∘ weyl v' =
      (fun ψ => Complex.exp (((Real.pi * omega n v v' / 2 : ℝ) : ℂ) * Complex.I) • ψ)
        ∘ weyl (v + v')) ∧
    (∀ (v : PhaseSpace n) (a b : ℝ), weyl (a • v) ∘ weyl (b • v) = weyl ((a + b) • v)) := by sorry

end CVStabilizer
