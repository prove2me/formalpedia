-- Prove2me | Theorems.Thm_BenignDegen_proposition_B_1
-- name    : BenignDegen.proposition_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:10.28102+00:00
-- url     : https://prove2.me/theorems/c25754d6-c434-4aa1-b5d8-692f2234758b
-- title:
--   Proposition B.1 — the independent encoding $\mathcal A_d$ has full row rank and $\{X:\mathcal A_dX=e_1\}=I_N+\mathcal T_d$
-- statement:
--   Fix $1\le d\le n$, and for each XOR class $\Gamma$ choose a reference pair $\{A,B\}$ with $A\triangle B=\Gamma$ (the pair $\{\emptyset,\emptyset\}$ for $\Gamma=\emptyset$). Let $D_1,\dots,D_{m-1}$ be the consistency matrices $D_{A,B}=F_{A,B}-F^\circ_{A\triangle B}$ of all non-reference pairs, and $\mathcal A_dX=(X_{\emptyset,\emptyset},\langle D_1,X\rangle,\dots,\langle D_{m-1},X\rangle)$, $b=e_1$ (B.3). Then $D_1,\dots,D_{m-1}$ form a basis of $\ker(\mathcal G_d)=\mathcal H_d^\perp$, $\mathcal A_d$ has full row rank, and
--
--   $$
--   \{X:\mathcal A_dX=e_1\}=I_N+\mathcal T_d,\qquad \ker(\mathcal A_d)=\mathcal T_d,\qquad \operatorname{ran}(\mathcal A_d^*)=\mathcal R_d,\qquad \mathcal A_d^\dagger e_1=I_N, \tag{B.4}
--   $$
--
--   with $m=\frac{N(N+1)}2-|\mathcal I_{2d}|+1$ rows. This makes $(\mathrm P_d)$ a standard-form SDP with a surjective constraint map, the setting of §3.
--
--   Differences from the source:
--   - encoding: square-free f, I_d, {±1}ⁿ, '≡ (mod I_B)' → coefficient function Finset (Fin n) → ℝ, {T : Finset (Fin n) // T.card ≤ d}, Fin n → ℤˣ, equality of square-free coefficients through G_d (B.2); reason: the same objects; I_d = {T : |T| ≤ min{d, n}} because |T| ≤ n always
--   - encoding: unordered pairs {A, B}; one reference pair per XOR class → Sym2 I_d; a function ref : Finset (Fin n) → Sym2 I_d whose value at every occurring class lies in that class, with ref ∅ = {∅, ∅}; reason: the same choice data; the statement is for every such choice
--   - encoding: m = N(N + 1)/2 − |I_{2d}| + 1 → card(rows) + |I_{2d}| = N(N + 1)/2 + 1; reason: avoids natural-number subtraction; the same number
--   - encoding: D₁, …, D_{m−1} form a basis of ker(G_d) = H_d^⊥; full row rank → linear independence and span = H_d^⊥, plus {Y : G_d(Y) = 0} = H_d^⊥; A_d surjective; reason: the same assertions
--   - encoding: the row X_{∅,∅} → ⟨F_{∅,∅}, X⟩; reason: F_{∅,∅} = E_{∅,∅}, so the two are equal
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix B, (B.3), Proposition B.1, (B.4), p.14

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Proposition B.1 (exact standard SDP encoding), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.14.
For every choice of reference pairs (one per XOR class, `{∅, ∅}` for `Γ = ∅`), the consistency
matrices `D_j` of (B.3) form a basis of `ker(G_d) = H_d^⊥`, the operator `A_d` of (B.3) has full
row rank, and (B.4) holds: `{X : A_d X = e_1} = I_N + T_d`, `ker(A_d) = T_d`, `ran(A_d^*) = R_d`,
`A_d^† e_1 = I_N`; the number of rows is `m = N(N + 1)/2 − |I_{2d}| + 1`.

**Formalization Note** `m = N(N+1)/2 − |I_{2d}| + 1` is stated without natural subtraction as
`m + |I_{2d}| = N(N+1)/2 + 1`. -/
theorem proposition_B_1 (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n)
    (ref : Finset (Fin n) → Sym2 (Idx n d)) (href : IsRefChoice ref) :
    LinearIndependent ℝ (consistencyMat ref) ∧
    Submodule.span ℝ (Set.range (consistencyMat ref)) = (Hd n d)ᗮ ∧
    {Y : SymMat (Idx n d) | Gd n d Y = 0} = ((Hd n d)ᗮ : Set (SymMat (Idx n d))) ∧
    Function.Surjective (encB3 ref) ∧
    {X : SymMat (Idx n d) | encB3 ref X = e1 ref} = {X | X - IdMat (Idx n d) ∈ Td n d} ∧
    LinearMap.ker (encB3 ref : SymMat (Idx n d) →ₗ[ℝ] EuclideanSpace ℝ (B3Row ref)) = Td n d ∧
    LinearMap.range (ContinuousLinearMap.adjoint (encB3 ref) :
      EuclideanSpace ℝ (B3Row ref) →ₗ[ℝ] SymMat (Idx n d)) = Rd n d ∧
    ({ A := encB3 ref, b := e1 ref, C := 0 } : SDPData (Idx n d) (B3Row ref)).Apinv (e1 ref) =
      IdMat (Idx n d) ∧
    Fintype.card (B3Row ref) + (I2d n d).card = Nd n d * (Nd n d + 1) / 2 + 1 := by sorry

end BenignDegen
