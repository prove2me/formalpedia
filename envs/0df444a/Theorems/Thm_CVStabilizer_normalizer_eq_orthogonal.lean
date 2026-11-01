-- Prove2me | Theorems.Thm_CVStabilizer_normalizer_eq_orthogonal
-- name    : CVStabilizer.normalizer_eq_orthogonal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:14.110854+00:00
-- url     : https://prove2.me/theorems/d7e9d67c-68bd-4805-8230-696f553602f9
-- title:
--   The operators commuting with $S$ (the normalizer $N(S)$) correspond to $W^\omega$
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb R^{2n}$ satisfy $\omega(u_i,u_j)=0$, let $W=\operatorname{span}_{\mathbb R}\{u_i\}$, $S=\{U(w):w\in W\}$, and let $W^\omega=\{v:\omega(v,u_i)=0\ \forall i\}$ be the symplectic orthogonal. For every $v\in\mathbb R^{2n}$:
--
--   1. $U(v)$ commutes with every element of $S$ if and only if $v\in W^\omega$;
--   2. $U(v)\,U(w)\,U(v)^{-1}\in S$ for every $w\in W$ (with $U(v)^{-1}=U(-v)$) if and only if $v\in W^\omega$.
--
--   So the normalizer $N(S)$, which the paper identifies with the operators commuting with $S$, corresponds exactly to $W^\omega$. Real coefficients matter here: for an integer lattice in place of $W$ the condition would be $\omega(v,w)\in 2\mathbb Z$ instead.
--
--   **Formalization Note** $U$ is the concrete realization $(U(s,t)\psi)(x)=e^{i\pi(\langle t,x\rangle+\langle s,t\rangle/2)}\psi(x+s)$ acting on all functions $\mathbb R^n\to\mathbb C$; operators are composed with $\circ$ and a scalar $c$ acts as $\psi\mapsto c\,\psi$.
--
--   Differences from the source:
--   - reading: U(v) = exp(iπ Σᵢ (sᵢp̂ᵢ + tᵢq̂ᵢ)) with [q̂, p̂] = 1 (2), which under no normalization of the canonical pair yields (3) as printed → the concrete realization weyl: (U(s,t)ψ)(x) = e^{iπ(⟨t,x⟩ + ⟨s,t⟩/2)} ψ(x + s); reason: (3), (7) and every example of the paper use (3); in this realization (3) and (7) hold verbatim, Z(t) = U(0,t) is the multiplication by e^{iπtx} of (11), X(s) = U(s,0) is the position shift ψ ↦ ψ(· + s), i.e. X(s)|q⟩ = |q − s⟩ (this direction is forced by (3) once Z(t) is the multiplication of (11); the p.3 example X̄(q)|000⟩ = |qqq⟩ reads the shift the other way, which is the paper's inconsistency, and no item depends on it), and the symmetric phase e^{iπ⟨s,t⟩/2} gives U(av)U(bv) = U((a+b)v)
--   - generalization: operators on the state space with position basis |q⟩ → operators on all functions ℝⁿ → ℂ; identities hold pointwise; reason: the position eigenvectors |q⟩ are not in L²; each U(v) is a shift followed by multiplication by a continuous phase, so it preserves L² and a.e. equality, every operator identity restricts to L²(ℝⁿ), and equality, commutation and injectivity of the U(v) are the same on L² as on all functions
--   - encoding: Gn = {X(s₁)Z(t₁) ⊗ ⋯ ⊗ X(sₙ)Z(tₙ)} (1), whose typical member is U(v) (2) → the Pauli operators are the U(v), v ∈ ℝ²ⁿ; global phases are not tracked; reason: X(s)Z(t) = e^{iπ⟨s,t⟩/2}U(s,t), and a scalar phase changes no commutation or conjugation statement
--   - encoding: W^ω = {v : ω(v, uᵢ) = 0 ∀i} → (omega n).orthogonal W = {v | ∀ w ∈ W, ω(w, v) = 0}; reason: equal sets, by antisymmetry and linearity of ω
--   - reading: 'the operators commuting with S, namely the normalizer N(S) of S' → both the commutant {v : U(v) commutes with S} and the normalizer {v : U(v)U(w)U(−v) ∈ S for all w ∈ W} are shown equal to W^ω; reason: the page identifies the two; stating both makes neither reading the weaker one
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, p.2, left column ("Since any operator which commutes with everything in S… is the symplectic orthogonal W ω = {v : ω(v, ui) = 0∀i}")

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **The normalizer is the symplectic orthogonal**, Barnes, arXiv:quant-ph/0405064v1, p.2, left
column: "In our symplectic language, an observable commuting with S corresponds to a vector v such
that ω(v, uᵢ) = 0 for all i, so that if the uᵢ span a subspace W ⊆ ℝ²ⁿ, then the space of
operators commuting with S is the symplectic orthogonal W^ω = {v : ω(v, uᵢ) = 0 ∀i}."
With `ω(uᵢ, uⱼ) = 0`, `W = span uᵢ` and `S = {U(w) : w ∈ W}`, for every `v ∈ ℝ²ⁿ`:

1. `U(v)` commutes with every element of `S` iff `v ∈ W^ω`;
2. `U(v)` normalizes `S` (`U(v) U(w) U(v)⁻¹ ∈ S` for all `w ∈ W`, with `U(v)⁻¹ = U(−v)`) iff
   `v ∈ W^ω`. The page calls this group "the normalizer N(S) of S".

The coefficients are real: for `w ∈ W` every multiple `aw` lies in `W`, and this is what forces
`ω(v, w) = 0` rather than `ω(v, w) ∈ 2ℤ` as for the lattices of the paper's reference [9].

**Formalization Note** `W^ω` is Mathlib's `(omega n).orthogonal W = {v | ∀ w ∈ W, ω(w, v) = 0}`;
by antisymmetry and linearity of `ω` this is the page's `{v : ω(v, uᵢ) = 0 ∀i}`. -/
theorem normalizer_eq_orthogonal (n k : ℕ) (u : Fin k → PhaseSpace n)
    (hiso : ∀ i j, omega n (u i) (u j) = 0) :
    let W : Submodule ℝ (PhaseSpace n) := Submodule.span ℝ (Set.range u)
    let Wω : Submodule ℝ (PhaseSpace n) := (omega n).orthogonal W
    (∀ v : PhaseSpace n, (∀ w ∈ W, weyl v ∘ weyl w = weyl w ∘ weyl v) ↔ v ∈ Wω) ∧
    (∀ v : PhaseSpace n,
      (∀ w ∈ W, ∃ w' ∈ W, weyl v ∘ weyl w ∘ weyl (-v) = weyl w') ↔ v ∈ Wω) := by sorry

end CVStabilizer
