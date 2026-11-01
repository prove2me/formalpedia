-- Prove2me | Theorems.Thm_CVStabilizer_logical_weyl_relations
-- name    : CVStabilizer.logical_weyl_relations
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:08.801428+00:00
-- url     : https://prove2.me/theorems/52ce9f9f-a4d3-4cc3-9aa5-b336550c4b8f
-- title:
--   Eq. (7): the logical operators satisfy $U(s\,x_i)U(t\,z_j)=e^{i\pi st\delta_{ij}}U(t\,z_j)U(s\,x_i)$ (printed comma read as a product)
-- statement:
--   Let $x_1,z_1,\dots,x_m,z_m\in\mathbb R^{2n}$ satisfy $\omega(x_i,x_j)=\omega(z_i,z_j)=0$ and $\omega(x_i,z_j)=\delta_{ij}$. Then for all $i,j$ and all real $s,t$,
--
--   $$
--   [U(s\,x_i),U(t\,x_j)]=[U(s\,z_i),U(t\,z_j)]=0,\qquad U(s\,x_i)\,U(t\,z_j)=e^{i\pi st\delta_{ij}}\,U(t\,z_j)\,U(s\,x_i). \tag{7}
--   $$
--
--   Applied to the basis of $W^\omega/W$ (with $m=n-k$), these are the commutation relations of $n-k$ independent position and momentum shifts.
--
--   **Formalization Note** $U$ is the concrete realization $(U(s,t)\psi)(x)=e^{i\pi(\langle t,x\rangle+\langle s,t\rangle/2)}\psi(x+s)$ acting on all functions $\mathbb R^n\to\mathbb C$; operators are composed with $\circ$ and a scalar $c$ acts as $\psi\mapsto c\,\psi$. Commutators $[A,B]=0$ are stated as $A\circ B=B\circ A$.
--
--   Differences from the source:
--   - reading: U(v) = exp(iπ Σᵢ (sᵢp̂ᵢ + tᵢq̂ᵢ)) with [q̂, p̂] = 1 (2), which under no normalization of the canonical pair yields (3) as printed → the concrete realization weyl: (U(s,t)ψ)(x) = e^{iπ(⟨t,x⟩ + ⟨s,t⟩/2)} ψ(x + s); reason: (3), (7) and every example of the paper use (3); in this realization (3) and (7) hold verbatim, Z(t) = U(0,t) is the multiplication by e^{iπtx} of (11), X(s) = U(s,0) is the position shift ψ ↦ ψ(· + s), i.e. X(s)|q⟩ = |q − s⟩ (this direction is forced by (3) once Z(t) is the multiplication of (11); the p.3 example X̄(q)|000⟩ = |qqq⟩ reads the shift the other way, which is the paper's inconsistency, and no item depends on it), and the symmetric phase e^{iπ⟨s,t⟩/2} gives U(av)U(bv) = U((a+b)v)
--   - generalization: operators on the state space with position basis |q⟩ → operators on all functions ℝⁿ → ℂ; identities hold pointwise; reason: the position eigenvectors |q⟩ are not in L²; each U(v) is a shift followed by multiplication by a continuous phase, so it preserves L² and a.e. equality, every operator identity restricts to L²(ℝⁿ), and equality, commutation and injectivity of the U(v) are the same on L² as on all functions
--   - generalization: the basis x₁, z₁, …, x_{n−k}, z_{n−k} of W^ω/W constructed from a stabilizer → any vectors x₁, z₁, …, x_m, z_m ∈ ℝ²ⁿ with ω(xᵢ, xⱼ) = ω(zᵢ, zⱼ) = 0, ω(xᵢ, zⱼ) = δᵢⱼ; reason: the proof uses only these relations; the logical basis (m = n − k) satisfies them
--   - reading: U(s xᵢ)U(t zⱼ) = e^{iπstδᵢⱼ}U(t zⱼ), U(s xᵢ) (7), and [A, B] = 0 → U(s xᵢ) ∘ U(t zⱼ) = e^{iπstδᵢⱼ} • U(t zⱼ) ∘ U(s xᵢ); commutators as A ∘ B = B ∘ A; reason: the comma is a printing slip; with it removed (7) agrees with (3), since ω(s xᵢ, t zⱼ) = st δᵢⱼ
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, eq. (7), p.2

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **The logical Weyl relations, (7)**, Barnes, arXiv:quant-ph/0405064v1, p.2: "The group of
operators corresponding to this basis satisfies [U(s xᵢ), U(t xⱼ)] = [U(s zᵢ), U(t zⱼ)] = 0 and
U(s xᵢ)U(t zⱼ) = e^{iπstδᵢⱼ}U(t zⱼ) U(s xᵢ), (7)". For any vectors `x₁, z₁, …, x_m, z_m ∈ ℝ²ⁿ`
with `ω(xᵢ, xⱼ) = ω(zᵢ, zⱼ) = 0` and `ω(xᵢ, zⱼ) = δᵢⱼ`, and all real `s, t`:
`U(s xᵢ)` and `U(t xⱼ)` commute, `U(s zᵢ)` and `U(t zⱼ)` commute, and
`U(s xᵢ)U(t zⱼ) = e^{iπ s t δᵢⱼ} U(t zⱼ)U(s xᵢ)`.

**Formalization Note** The page prints "U(t zⱼ), U(s xᵢ)" with a stray comma; the product is
meant. Commutators `[A, B] = 0` are stated as `A ∘ B = B ∘ A`. The statement is for any family
with the three `ω`-relations, in particular for the basis of `exists_logical_basis` (`m = n − k`). -/
theorem logical_weyl_relations (n m : ℕ) (x z : Fin m → PhaseSpace n)
    (hxx : ∀ i j, omega n (x i) (x j) = 0) (hzz : ∀ i j, omega n (z i) (z j) = 0)
    (hxz : ∀ i j, omega n (x i) (z j) = if i = j then 1 else 0) :
    ∀ (i j : Fin m) (s t : ℝ),
      weyl (s • x i) ∘ weyl (t • x j) = weyl (t • x j) ∘ weyl (s • x i) ∧
      weyl (s • z i) ∘ weyl (t • z j) = weyl (t • z j) ∘ weyl (s • z i) ∧
      weyl (s • x i) ∘ weyl (t • z j) =
        (fun ψ => Complex.exp
            (((Real.pi * s * t * (if i = j then 1 else 0) : ℝ) : ℂ) * Complex.I) • ψ)
          ∘ weyl (t • z j) ∘ weyl (s • x i) := by sorry

end CVStabilizer
