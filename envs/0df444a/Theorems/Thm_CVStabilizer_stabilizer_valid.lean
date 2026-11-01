-- Prove2me | Theorems.Thm_CVStabilizer_stabilizer_valid
-- name    : CVStabilizer.stabilizer_valid
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:03.615459+00:00
-- url     : https://prove2.me/theorems/26eb2bb7-5ca0-4401-bcdc-f9002278013c
-- title:
--   Eq. (4): $S=\{U(w):w\in W\}$ is an abelian subgroup not containing $-I$, a valid stabilizer
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb R^{2n}$ satisfy $\omega(u_i,u_j)=0$ for all $i,j$, let $W=\operatorname{span}_{\mathbb R}\{u_i\}$, and let
--
--   $$
--   S=\Big\{U(v):v=\sum_{i=1}^k a_iu_i,\ a_i\in\mathbb R\Big\}. \tag{4}
--   $$
--
--   Then:
--
--   1. $U(w)U(w')=U(w+w')$ for all $w,w'\in W$, and $U(0)=I$, so $S$ is a group (with $U(w)^{-1}=U(-w)$);
--   2. any two elements of $S$ commute;
--   3. $v\mapsto U(v)$ is one-to-one, so $S$ is in one-to-one correspondence with $W$;
--   4. $U(v)\neq -I$ for every $v$, so $-I\notin S$.
--
--   These are Gottesman's two conditions (any two elements commute, $-I\notin S$) that make $S$ a valid stabilizer.
--
--   **Formalization Note** $U$ is the concrete realization $(U(s,t)\psi)(x)=e^{i\pi(\langle t,x\rangle+\langle s,t\rangle/2)}\psi(x+s)$ acting on all functions $\mathbb R^n\to\mathbb C$; operators are composed with $\circ$ and a scalar $c$ acts as $\psi\mapsto c\,\psi$.
--
--   Differences from the source:
--   - reading: U(v) = exp(iπ Σᵢ (sᵢp̂ᵢ + tᵢq̂ᵢ)) with [q̂, p̂] = 1 (2), which under no normalization of the canonical pair yields (3) as printed → the concrete realization weyl: (U(s,t)ψ)(x) = e^{iπ(⟨t,x⟩ + ⟨s,t⟩/2)} ψ(x + s); reason: (3), (7) and every example of the paper use (3); in this realization (3) and (7) hold verbatim, Z(t) = U(0,t) is the multiplication by e^{iπtx} of (11), X(s) = U(s,0) is the position shift ψ ↦ ψ(· + s), i.e. X(s)|q⟩ = |q − s⟩ (this direction is forced by (3) once Z(t) is the multiplication of (11); the p.3 example X̄(q)|000⟩ = |qqq⟩ reads the shift the other way, which is the paper's inconsistency, and no item depends on it), and the symmetric phase e^{iπ⟨s,t⟩/2} gives U(av)U(bv) = U((a+b)v)
--   - generalization: operators on the state space with position basis |q⟩ → operators on all functions ℝⁿ → ℂ; identities hold pointwise; reason: the position eigenvectors |q⟩ are not in L²; each U(v) is a shift followed by multiplication by a continuous phase, so it preserves L² and a.e. equality, every operator identity restricts to L²(ℝⁿ), and equality, commutation and injectivity of the U(v) are the same on L² as on all functions
--   - encoding: Gn = {X(s₁)Z(t₁) ⊗ ⋯ ⊗ X(sₙ)Z(tₙ)} (1), whose typical member is U(v) (2) → the Pauli operators are the U(v), v ∈ ℝ²ⁿ; global phases are not tracked; reason: X(s)Z(t) = e^{iπ⟨s,t⟩/2}U(s,t), and a scalar phase changes no commutation or conjugation statement
--   - generalization: S in one-to-one correspondence with the span W → v ↦ U(v) is injective on all of ℝ²ⁿ; reason: specializes to injectivity on W
--   - generalization: −I is not in S → U(v) ≠ −I for every v ∈ ℝ²ⁿ; reason: specializes to v ∈ W
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, eq. (4) and the sentence after it, p.1; conditions (1)–(2) and "… and thus a valid stabilizer", p.2, left column

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **`S` is a valid stabilizer, (4)**, Barnes, arXiv:quant-ph/0405064v1, pp.1–2. For
`u₁, …, u_k ∈ ℝ²ⁿ` with `ω(uᵢ, uⱼ) = 0` for all `i, j`, let `W` be their real span and
`S = {U(v) : v = Σᵢ aᵢuᵢ, aᵢ ∈ ℝ}` (4). Then

1. `S` is closed under products, `U(w)U(w′) = U(w + w′)` for `w, w′ ∈ W`, and contains
   `U(0) = I` (a subgroup, with `U(w)⁻¹ = U(−w)`);
2. any two elements of `S` commute ("This subgroup S is actually abelian", p.1, condition (1)
   of p.2);
3. `v ↦ U(v)` is one-to-one ("in one-to-one correspondence with the span", p.1);
4. no `U(v)` equals `−I` (condition "(2) −I is not in S", p.2).

**Formalization Note** `U` is `weyl`, acting on all functions `ℝⁿ → ℂ`. Items 3 and 4 are stated
for every `v ∈ ℝ²ⁿ`, which contains the claims for `v ∈ W`. Linear independence of the `uᵢ` is
not needed and is not assumed. -/
theorem stabilizer_valid (n k : ℕ) (u : Fin k → PhaseSpace n)
    (hiso : ∀ i j, omega n (u i) (u j) = 0) :
    let W : Submodule ℝ (PhaseSpace n) := Submodule.span ℝ (Set.range u)
    (∀ w ∈ W, ∀ w' ∈ W, weyl w ∘ weyl w' = weyl (w + w')) ∧
    (∀ w ∈ W, ∀ w' ∈ W, weyl w ∘ weyl w' = weyl w' ∘ weyl w) ∧
    weyl (0 : PhaseSpace n) = id ∧
    Function.Injective (weyl (n := n)) ∧
    (∀ v : PhaseSpace n, weyl v ≠ fun ψ => -ψ) := by sorry

end CVStabilizer
