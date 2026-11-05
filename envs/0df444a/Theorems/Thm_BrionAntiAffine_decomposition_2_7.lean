-- Prove2me | Theorems.Thm_BrionAntiAffine_decomposition_2_7
-- name    : BrionAntiAffine.decomposition_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:47.663566+00:00
-- url     : https://prove2.me/theorems/b10bdd1d-23de-45a9-9e17-6393d38b4a30
-- title:
--   §2.3, (2.5)–(2.7) — $G\simeq G/U\times_A G/T$
-- statement:
--   Let $k$ have characteristic $0$ and let $(G,\alpha)$ be anti-affine over the abelian variety $A$. Then $G_{\mathrm{aff}}$ is a connected commutative algebraic group with a unique decomposition
--
--   $$G_{\mathrm{aff}}=T\times U\tag{2.5}$$
--
--   where $T$ is a torus and $U$ is connected and unipotent, and $U$ has a unique structure of $k$-vector space. Further, $G/U$ is an extension of $A$ by $T$, $G/T$ is a vector extension of $A$ by $U$, $\alpha=\alpha_{G/T}\,p_T=\alpha_{G/U}\,p_U$, and the square (2.6) is cartesian, which yields the isomorphism
--
--   $$G\xrightarrow{\ \sim\ }G/U\times_A G/T\tag{2.7}$$
--
--   of algebraic groups over $A$. Moreover the lattice invariant of $G$ equals that of $G/U$, and the subspace invariant of $G$ equals that of $G/T$.
--
--   This splits the classification in characteristic $0$ into its two halves.
--
--   **Formalization Note** $G/U$ and $G/T$ are given as groups $S,W$ with quotient maps, not as constructed quotients. $G_{\mathrm{aff}}=T\times U$ says the multiplication map $T\times U\to G$ is a homomorphism and is the kernel of $\alpha$. Uniqueness is up to isomorphism over $G$.
--
--   Differences from the source:
--   - encoding: Gaff = T × U, T a torus, U connected and unipotent → jT, jU with mulMap jT jU a homomorphism and the kernel of α; U a vector group, connected and unipotent; uniqueness against every torus and connected unipotent pair; reason: Gaff is the kernel of α by IsChevalleyQuotient; commutativity of T × U gives that of Gaff
--   - encoding: U has a unique structure of k-vector space → any two trivializations of U as a vector group differ by a k-matrix; reason: a k-vector space structure on the group scheme U is such a trivialization up to GL_n(k)
--   - encoding: the quotients G/U, G/T → groups S, W with pU, pT such that jU → G → S and jT → G → W are exact; reason: the quotient of G by a normal subgroup scheme is characterized by this exactness
--   - generalization: the printed display ends at (2.7) → adds the conjuncts latticeSet αS = latticeSet α and vSet αW = vSet α; reason: connects the quotients to the kernel form used by the goal; dropping them gives the printed statement
--   - encoding: a group scheme over A: a connected G with G/Gaff ≃ A → a homomorphism α with IsChevalleyQuotient: faithfully flat quasi-compact, connected affine kernel, and every such β to an abelian variety factors through α; reason: the two are the same data, since a subgroup scheme lies in ker β exactly when β factors through the quotient by it; connectedness of G follows
--   - encoding: an anti-affine algebraic group (smooth by the conventions of p.3) → G : AntiAffineOver A, with no smoothness hypothesis; reason: in characteristic 0 every group scheme of finite type is smooth (Cartier), so the instances are the same
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, §2.3, (2.5)–(2.7), p.9

import Mathlib
import Definitions.Def_BrionAntiAffine_IsTorus
import Definitions.Def_BrionAntiAffine_IsVectorGroup
import Definitions.Def_BrionAntiAffine_IsUnipotent

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- §2.3, (2.5)–(2.7), Brion, arXiv:0710.5211v3, p.9. In characteristic `0`, let `G` be anti-affine over
`A`. Then `Gaff` is a connected commutative algebraic group and has a unique decomposition
`Gaff = T × U` (2.5), with `T` a torus and `U` connected unipotent; `U` has a unique structure of
`k`-vector space; `G/U` is an extension of `A` by `T`, `G/T` is a vector extension of `A` by `U`, and
the square (2.6) is cartesian, giving the isomorphism `G ≃ G/U ×_A G/T` of (2.7) over `A`.

**Formalization Note.** `S`, `W` are `G/U`, `G/T`. `jT`, `jU` are the inclusions of `T`, `U`; that
`mulMap jT jU` is a homomorphism and is the kernel of `α` says `Gaff = T × U` as groups, which gives
commutativity. Uniqueness of the decomposition is stated up to isomorphism over `G`, against every
torus and connected unipotent pair; uniqueness of the vector space structure says that two
trivializations of `U` differ by a `k`-linear map. The last two conjuncts, equating the invariants of
`G` with those of `S` and `W`, are an addition to the printed statement: they connect these quotients
to the kernel form of the invariants used by the goal. -/
theorem decomposition_2_7 [CharZero k] (A : Sch k) [GrpObj A]
    (G : AntiAffineOver A) :
    ∃ (T U S W : Sch k) (_ : GrpObj T) (_ : GrpObj U) (_ : GrpObj S) (_ : GrpObj W)
      (jT : T ⟶ G.G) (jU : U ⟶ G.G) (iT : T ⟶ S) (iU : U ⟶ W)
      (pU : G.G ⟶ S) (pT : G.G ⟶ W) (αS : S ⟶ A) (αW : W ⟶ A),
      IsTorus T ∧ IsVectorGroup U ∧ IsAlgebraicGroup T ∧ IsAlgebraicGroup U ∧
      ConnectedSpace U.left ∧ IsUnipotent U ∧
      IsMonHom jT ∧ IsMonHom jU ∧
      IsMonHom (mulMap jT jU) ∧ IsPullback (mulMap jT jU) (toUnit (T ⊗ U)) G.α η[A] ∧
      (∀ (T' U' : Sch k) [GrpObj T'] [GrpObj U'] (jT' : T' ⟶ G.G) (jU' : U' ⟶ G.G),
        IsTorus T' → IsUnipotent U' → ConnectedSpace U'.left →
        IsMonHom jT' → IsMonHom jU' → IsMonHom (mulMap jT' jU') →
        IsPullback (mulMap jT' jU') (toUnit (T' ⊗ U')) G.α η[A] →
          ∃ (eT : T ≅ T') (eU : U ≅ U'), eT.hom ≫ jT' = jT ∧ eU.hom ≫ jU' = jU) ∧
      (∀ (n n' : ℕ) (e : VectorTrivialization U n) (e' : VectorTrivialization U n'),
        ∃ M : Matrix (Fin n') (Fin n) k, ∀ (S' : Sch k) (x : S' ⟶ U),
          e'.e S' x = (M.map (constants S')).mulVec (e.e S' x)) ∧
      IsExactSeq jU pU ∧ IsExactSeq jT pT ∧ IsExactSeq iT αS ∧ IsExactSeq iU αW ∧
      jT ≫ pU = iT ∧ jU ≫ pT = iU ∧ pU ≫ αS = G.α ∧ pT ≫ αW = G.α ∧
      IsPullback pU pT αS αW ∧
      latticeSet αS = latticeSet G.α ∧ vSet αW = vSet G.α := by sorry

end BrionAntiAffine
