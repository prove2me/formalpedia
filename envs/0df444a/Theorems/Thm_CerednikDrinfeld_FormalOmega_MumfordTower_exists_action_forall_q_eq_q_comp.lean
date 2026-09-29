-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_action_forall_q_eq_q_comp
-- name    : CerednikDrinfeld.FormalOmega.MumfordTower.exists_action_forall_q_eq_q_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/0132b679-86c6-5ccd-858e-4c523b289e0d
-- title:
--   Normaliser action on the levels of a Mumford tower
-- statement:
--   Fix a commutative ring $\mathcal O$, an element $\pi \in \mathcal O$, a field $K_0$ that is an $\mathcal O$-algebra, a natural number $r$, an element $g_1 \in \mathrm{GL}_2(K_0)$, a subgroup $N \le \mathrm{PGL}(2,K_0)$, and a Mumford tower $D$ for these data, so in particular $D$ provides schemes $D.Z\,n$, structure morphisms $D.zb\,n : D.Z\,n \to \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$, transition morphisms $D.zt\,n : D.Z\,n \to D.Z\,(n+1)$, and for each $\mathcal O$-algebra $B$ with $(\pi \cdot 1_B)^{n+1} = 0$ a map $D.q\,n\,B$ sending a Deligne datum over $B$ (an assignment of a $B$-submodule $\mathrm{line}\,M \subseteq B \otimes_{\mathcal O} M$ to each full lattice $M \subseteq K_0^2$, with invertible quotients, monotone in $M$, equivariant for homothetic matrices, and nondegenerate at each prime of $B$) to a morphism $\operatorname{Spec} B \to D.Z\,n$. The assertion is that there is a family $a$ attaching to every $g \in \mathrm{GL}_2(K_0)$ whose image $\bar g$ in $\mathrm{PGL}(2,K_0)$ satisfies $x \in N \iff \bar g x \bar g^{-1} \in N$ for all $x$, together with a proof of this condition, and to every $n$, an isomorphism $a_{g,n} : D.Z\,n \cong D.Z\,n$ such that: $a_{g,n}$ followed by $D.zb\,n$ equals $D.zb\,n$; $D.zt\,n$ followed by $a_{g,n+1}$ equals $a_{g,n}$ followed by $D.zt\,n$; for every $\mathcal O$-algebra $B$ with $(\pi \cdot 1_B)^{n+1} = 0$ and all Deligne data $P, P'$ over $B$ such that $P'$ is the pullback of $P$ along $g^{-1}$, i.e. $P'.\mathrm{line}\,M$ is the preimage of $P.\mathrm{line}(g^{-1} \cdot M)$ under the base-changed action isomorphism for every full lattice $M$, one has $D.q\,n\,B\,P' = D.q\,n\,B\,P$ followed by $a_{g,n}$; $a_{g,n}$ is the unique endomorphism of $D.Z\,n$ with this last property; $a_{g,n}$ is the identity whenever $\bar g \in N$; and $a_{gg',n} = a_{g,n} \circ a_{g',n}$ for any two such $g, g'$ (with a proof that $\overline{gg'}$ also normalises $N$).
--
--   This is the statement that the normaliser of $N$ in $\mathrm{PGL}(2,K_0)$ acts on each level of a Mumford tower, compatibly with the base $\operatorname{Spec}(\mathcal O/\pi^{n+1})$, with the transition maps and with the parametrisation of points by Deligne data, the action being trivial on $N$ itself. It is repackaged as a group homomorphism into the automorphisms of the tower by [`CerednikDrinfeld.FormalOmega.MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le`](thm.html#CerednikDrinfeld.FormalOmega.MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le), in the course of the Čerednik–Drinfeld description of the formal upper half plane and its quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_action_forall_q_eq_q_comp.lean

import Definitions.Def_CerednikDrinfeld_MumfordTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.exists_action_forall_q_eq_q_comp
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (D : MumfordTower 𝒪 π K₀ r g₁ N) :
    ∃ a : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀),
        (∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g * x * (Matrix.ProjGenLinGroup.mk g)⁻¹ ∈ N) → ∀ n : ℕ, D.Z n ≅ D.Z n,

      (∀ g hg (n : ℕ), (a g hg n).hom ≫ D.zb n = D.zb n) ∧

      (∀ g hg (n : ℕ), D.zt n ≫ (a g hg (n + 1)).hom = (a g hg n).hom ≫ D.zt n) ∧

      (∀ g hg (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' →
        D.q n B hB P' = D.q n B hB P ≫ (a g hg n).hom) ∧

      (∀ g hg (n : ℕ) (b : D.Z n ⟶ D.Z n),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' →
          D.q n B hB P' = D.q n B hB P ≫ b) → b = (a g hg n).hom) ∧

      (∀ g hg (n : ℕ), Matrix.ProjGenLinGroup.mk g ∈ N → (a g hg n).hom = 𝟙 (D.Z n)) ∧

      (∀ g hg g' hg' (hgg' : ∀ x : PGL(2, K₀), x ∈ N ↔
          Matrix.ProjGenLinGroup.mk (g * g') * x * (Matrix.ProjGenLinGroup.mk (g * g'))⁻¹ ∈ N) (n : ℕ),
        (a (g * g') hgg' n).hom = (a g' hg' n).hom ≫ (a g hg n).hom) := by sorry
