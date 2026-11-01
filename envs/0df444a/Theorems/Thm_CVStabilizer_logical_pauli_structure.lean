-- Prove2me | Theorems.Thm_CVStabilizer_logical_pauli_structure
-- name    : CVStabilizer.logical_pauli_structure
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:11.233824+00:00
-- url     : https://prove2.me/theorems/940963f4-cf8c-4145-8efa-e53b9bb3ae5b
-- title:
--   The logical operators have the group structure of the $(n-k)$-mode Pauli group $G_{n-k}$
-- statement:
--   Let $x_1,z_1,\dots,x_m,z_m\in\mathbb R^{2n}$ satisfy $\omega(x_i,x_j)=\omega(z_i,z_j)=0$ and $\omega(x_i,z_j)=\delta_{ij}$, and define $\varphi:\mathbb R^{2m}\to\mathbb R^{2n}$ by $\varphi(a,b)=\sum_{i=1}^m(a_ix_i+b_iz_i)$. Then
--
--   1. $\varphi$ is injective;
--   2. $\varphi$ is symplectic: $\omega_n(\varphi(\alpha),\varphi(\beta))=\omega_m(\alpha,\beta)$;
--   3. the logical operators obey the product law of the $m$-mode Weyl operators:
--   $$
--   U(\varphi(\alpha))\,U(\varphi(\beta))=e^{i\pi\omega_m(\alpha,\beta)/2}\,U(\varphi(\alpha+\beta));
--   $$
--   4. $\varphi(e_i,0)=x_i$ and $\varphi(0,e_i)=z_i$, so $U(s\,x_i)$ and $U(s\,z_i)$ are the images of the position and momentum shifts of the $i$-th logical mode.
--
--   With $m=n-k$ and the basis of $W^\omega/W$, this is the statement that the logical operators form a copy of the generalized Pauli group $G_{n-k}$.
--
--   **Formalization Note** $U$ is the concrete realization $(U(s,t)\psi)(x)=e^{i\pi(\langle t,x\rangle+\langle s,t\rangle/2)}\psi(x+s)$ acting on all functions $\mathbb R^n\to\mathbb C$; operators are composed with $\circ$ and a scalar $c$ acts as $\psi\mapsto c\,\psi$.
--
--   Differences from the source:
--   - reading: U(v) = exp(iπ Σᵢ (sᵢp̂ᵢ + tᵢq̂ᵢ)) with [q̂, p̂] = 1 (2), which under no normalization of the canonical pair yields (3) as printed → the concrete realization weyl: (U(s,t)ψ)(x) = e^{iπ(⟨t,x⟩ + ⟨s,t⟩/2)} ψ(x + s); reason: (3), (7) and every example of the paper use (3); in this realization (3) and (7) hold verbatim, Z(t) = U(0,t) is the multiplication by e^{iπtx} of (11), X(s) = U(s,0) is the position shift ψ ↦ ψ(· + s), i.e. X(s)|q⟩ = |q − s⟩ (this direction is forced by (3) once Z(t) is the multiplication of (11); the p.3 example X̄(q)|000⟩ = |qqq⟩ reads the shift the other way, which is the paper's inconsistency, and no item depends on it), and the symmetric phase e^{iπ⟨s,t⟩/2} gives U(av)U(bv) = U((a+b)v)
--   - generalization: operators on the state space with position basis |q⟩ → operators on all functions ℝⁿ → ℂ; identities hold pointwise; reason: the position eigenvectors |q⟩ are not in L²; each U(v) is a shift followed by multiplication by a continuous phase, so it preserves L² and a.e. equality, every operator identity restricts to L²(ℝⁿ), and equality, commutation and injectivity of the U(v) are the same on L² as on all functions
--   - generalization: the basis x₁, z₁, …, x_{n−k}, z_{n−k} of W^ω/W constructed from a stabilizer → any vectors x₁, z₁, …, x_m, z_m ∈ ℝ²ⁿ with ω(xᵢ, xⱼ) = ω(zᵢ, zⱼ) = 0, ω(xᵢ, zⱼ) = δᵢⱼ; reason: the proof uses only these relations; the logical basis (m = n − k) satisfies them
--   - reading: 'has the same group structure as the generalized Pauli group G_{n−k}, with U(s xᵢ) and U(s zᵢ) acting as position and momentum shifts on the i-th logical mode' → φ(a, b) = Σᵢ (aᵢxᵢ + bᵢzᵢ) is injective and symplectic, U(φ(α))U(φ(β)) = e^{iπω_{n−k}(α,β)/2} U(φ(α+β)), φ(eᵢ, 0) = xᵢ, φ(0, eᵢ) = zᵢ; reason: this is the precise content of the phrase: the logical operators obey the (n − k)-mode product law of the Weyl operators, with xᵢ, zᵢ the images of the i-th position and momentum directions
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, p.2, left column, after (7) ("and thus has the same group structure as the generalized Pauli group Gn−k…")

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **The same group structure as `G_{n−k}`**, Barnes, arXiv:quant-ph/0405064v1, p.2: the group of
operators corresponding to the basis "has the same group structure as the generalized Pauli group
G_{n−k}, with the operators U(s xᵢ) and U(s zᵢ) acting as position and momentum shifts on the
i-th logical mode, respectively." For `x₁, z₁, …, x_m, z_m ∈ ℝ²ⁿ` with `ω(xᵢ, xⱼ) = ω(zᵢ, zⱼ) = 0`
and `ω(xᵢ, zⱼ) = δᵢⱼ`, let `φ : ℝ²ᵐ → ℝ²ⁿ`, `φ(a, b) = Σᵢ (aᵢxᵢ + bᵢzᵢ)`. Then

1. `φ` is injective;
2. `ω_n(φ(α), φ(β)) = ω_m(α, β)` (`φ` is symplectic);
3. the logical operators `U(φ(α))` obey the product law of the `m`-mode Weyl operators:
   `U(φ(α))U(φ(β)) = e^{iπω_m(α,β)/2} U(φ(α + β))`;
4. `φ` sends the `i`-th position-shift direction `(eᵢ, 0)` to `xᵢ` and the `i`-th momentum-shift
   direction `(0, eᵢ)` to `zᵢ`, so `U(s xᵢ) = U(φ(s eᵢ, 0))` and `U(s zᵢ) = U(φ(0, s eᵢ))` are the
   logical position and momentum shifts of mode `i`.

**Formalization Note** "Same group structure" is the product law of `weyl_mul` transported by
the symplectic embedding `φ`. The statement is for any family with the three `ω`-relations, in
particular for the basis of `exists_logical_basis` (`m = n − k`). -/
theorem logical_pauli_structure (n m : ℕ) (x z : Fin m → PhaseSpace n)
    (hxx : ∀ i j, omega n (x i) (x j) = 0) (hzz : ∀ i j, omega n (z i) (z j) = 0)
    (hxz : ∀ i j, omega n (x i) (z j) = if i = j then 1 else 0) :
    let φ : PhaseSpace m → PhaseSpace n := fun a => ∑ i, (a.1 i • x i + a.2 i • z i)
    Function.Injective φ ∧
    (∀ a b, omega n (φ a) (φ b) = omega m a b) ∧
    (∀ a b, weyl (φ a) ∘ weyl (φ b) =
      (fun ψ => Complex.exp (((Real.pi * omega m a b / 2 : ℝ) : ℂ) * Complex.I) • ψ)
        ∘ weyl (φ (a + b))) ∧
    (∀ i, φ (Pi.single i 1, 0) = x i ∧ φ (0, Pi.single i 1) = z i) := by sorry

end CVStabilizer
