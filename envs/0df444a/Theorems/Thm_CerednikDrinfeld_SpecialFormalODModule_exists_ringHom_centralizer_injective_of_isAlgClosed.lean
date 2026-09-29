-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_injective_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/79f7d957-d166-5fbd-9c4f-9e54dc79bed7
-- title:
--   Endomorphisms of a special formal mathcal O_D-module form an order
-- statement:
--   Let $p$ be a prime and let $k$ be an algebraically closed field of characteristic $p$, made a $\mathbb Z_{p^2} = W(\mathbb F_{p^2})$-algebra by a ring homomorphism $j \colon$ `Zp2 p` $\to k$. Let $\Phi$ be a special formal $\mathcal O_D$-module over $k$ for $j$ in the sense of the project's structure: a $2$-dimensional formal group law $F$ over $k$ together with a commutativity witness, a family of power-series endomorphisms $\mathrm{act}(a)$ of $F$ indexed by $a \in \mathbb Z_{p^2}$ which is multiplicative, additive and unital in $a$, and a further endomorphism $\varpi$ of $F$ with $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt-vector Frobenius $\sigma$; it is required in addition that the two pieces `lieZero` and `lieOne` of the tangent space attached to $j$ be complementary and each an invertible $k$-module (specialness), and that $\mathrm{act}(p)$ have kernel of degree $p^4$ (height $4$). Write $E$ for the centraliser, inside the endomorphism ring of $F$, of the set consisting of all $\mathrm{act}(a)$, $a \in \mathbb Z_{p^2}$, together with $\varpi$. Then there exist an injective ring homomorphism $\theta \colon E \to M_2(\mathbb Q_p)$ and a natural number $m$ such that every $M \in M_2(\mathbb Z_p)$ satisfies $p^m M \in \theta(E)$, and for every $e \in E$ the matrix $p^m \theta(e)$ lies in $M_2(\mathbb Z_p)$; that is, $p^m M_2(\mathbb Z_p) \subseteq \theta(E)$ and $p^m \theta(E) \subseteq M_2(\mathbb Z_p)$.
--
--   This is the statement that the ring of $\mathcal O_D$-linear endomorphisms of a special formal $\mathcal O_D$-module of height $4$ over an algebraically closed field of characteristic $p$ embeds in $M_2(\mathbb Q_p)$ as a subring commensurable with $M_2(\mathbb Z_p)$, so that its rational endomorphism algebra is $M_2(\mathbb Q_p)$ and its quasi-isogeny group is $GL_2(\mathbb Q_p)$. It feeds the results on isogenies of height $4$ between such modules and the combined existence statement used in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_injective_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ θ : Subring.centralizer
          (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) →+*
        Matrix (Fin 2) (Fin 2) ℚ_[p],
      Function.Injective θ ∧
      ∃ m : ℕ,
        (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
          ∃ e, θ e = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
        (∀ e, ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
          (p : ℚ_[p]) ^ m • θ e = M.map ((↑) : ℤ_[p] → ℚ_[p])) := by sorry
