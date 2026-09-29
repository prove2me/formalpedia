-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_existsUnique_hom_pullback_of_natural_of_invariant
-- name    : CerednikDrinfeld.FormalOmega.MumfordTower.existsUnique_hom_pullback_of_natural_of_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/67a37135-4639-5764-8302-af6422e2cf07
-- title:
--   Universal property of a base-changed level of a Mumford tower
-- statement:
--   Fix a commutative ring $\mathcal O$, an element $\pi \in \mathcal O$, a field $K_0$ that is an $\mathcal O$-algebra, a natural number $r$, an element $g_1 \in \mathrm{GL}_2(K_0)$, a subgroup $N \le \mathrm{PGL}(2,K_0)$, and a datum $D :$ `MumfordTower` $\mathcal O\,\pi\,K_0\,r\,g_1\,N$, that is, a tower of schemes $Z_m$ with proper flat structure morphisms $\mathrm{zb}_m : Z_m \to \operatorname{Spec}(\mathcal O/(\pi^{m+1}))$, cartesian transition squares, finite sets contained in affine opens, chart open immersions, and points $q_m(B,h_B,P) : \operatorname{Spec} B \to Z_m$ attached to Deligne data, natural in $B$, compatible with the tower and invariant under $N$. Fix $n$, an $\mathcal O$-algebra $C$ with $(\pi \text{ in } C)^{n+1} = 0$, a scheme $X'$, morphisms $p_1 : X' \to Z_n$, $p_2 : X' \to \operatorname{Spec} C$, and $s : \operatorname{Spec} C \to \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$ such that $s$ followed by $\operatorname{Spec}$ of $\mathcal O \to \mathcal O/(\pi^{n+1})$ is $\operatorname{Spec}$ of the structure map $\mathcal O \to C$, and such that the square formed by $p_1, p_2, \mathrm{zb}_n, s$ is cartesian. Fix a scheme $T$ and a rule $\rho$ assigning to every $\mathcal O$-algebra $B$ with $(\pi \text{ in } B)^{n+1} = 0$, every $\mathcal O$-algebra map $c : C \to B$ and every Deligne datum $P \in \Omega(B)$ a morphism $\rho_B(c,P) : \operatorname{Spec} B \to T$, subject to: (naturality) for $\varphi : B \to B'$ an $\mathcal O$-algebra map, $\rho_{B'}(\varphi \circ c, \varphi_* P)$ equals $\operatorname{Spec}\varphi$ followed by $\rho_B(c,P)$; (invariance) for $g \in \mathrm{GL}_2(K_0)$ whose class lies in $N$ and Deligne data $P, P'$ over $B$ with $P'$ the pullback of $P$ along $g^{-1}$ — that is, for every full lattice $M$ the line of $P'$ at $M$ is the preimage of the line of $P$ at $g^{-1}M$ under the base-changed action isomorphism — one has $\rho_B(c,P') = \rho_B(c,P)$. Then there is a unique morphism $w : X' \to T$ such that for all such $B$, $c$, $P$ and every $x : \operatorname{Spec} B \to X'$ with $x$ followed by $p_1$ equal to $q_n(B,h_B,P)$ and $x$ followed by $p_2$ equal to $\operatorname{Spec} c$, the composite $x$ followed by $w$ is $\rho_B(c,P)$.
--
--   This is the representability statement for the $n$-th level of a Mumford tower after base change along an $\mathcal O$-algebra $C$ killed by $\pi^{n+1}$: the fibre product $X' = Z_n \times_{\operatorname{Spec}\mathcal O/\pi^{n+1}} \operatorname{Spec} C$ receives a unique morphism compatible with any natural, $N$-invariant family of $T$-valued points indexed by Deligne data together with a $C$-structure. It is used in the construction of the descended quotient map for the Čerednik–Drinfel'd uniformisation, where the universal property pins down a morphism out of a base-changed level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordTower_existsUnique_hom_pullback_of_natural_of_invariant.lean

import Definitions.Def_CerednikDrinfeld_MumfordTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.existsUnique_hom_pullback_of_natural_of_invariant
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (D : MumfordTower 𝒪 π K₀ r g₁ N) (n : ℕ)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : (algebraMap 𝒪 C π) ^ (n + 1) = 0)
    (X' : Scheme.{0}) (p₁ : X' ⟶ D.Z n) (p₂ : X' ⟶ Spec (CommRingCat.of C))
    (s : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))
    (hX' : IsPullback p₁ p₂ (D.zb n) s)
    (T : Scheme.{0})
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (C →ₐ[𝒪] B) →
      (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ T))
    (hρnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (c : C →ₐ[𝒪] B)
      (P : (Omega K₀ π).obj B),
      ρ B' hB' (φ.comp c) ((Omega K₀ π).map φ P) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ρ B hB c P)
    (hρinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : C →ₐ[𝒪] B)
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk g ∈ N →
      ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → ρ B hB c P' = ρ B hB c P) :
    ∃! w : X' ⟶ T, ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : C →ₐ[𝒪] B)
      (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ X'),
      x ≫ p₁ = D.q n B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ w = ρ B hB c P := by sorry
