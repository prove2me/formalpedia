-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_eq_of_q_eq_of_natural_of_invariant
-- name    : CerednikDrinfeld.FormalOmega.MumfordTower.eq_of_q_eq_of_natural_of_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/735ebd49-7457-53cc-8994-b550b6230877
-- title:
--   Natural N-invariant families agree when the q-images agree
-- statement:
--   Fix a commutative ring $\mathcal O$, an element $\pi \in \mathcal O$, a field $K_0$ that is an $\mathcal O$-algebra, a natural number $r$, an element $g_1 \in \mathrm{GL}_2(K_0)$ and a subgroup $N \le \mathrm{PGL}_2(K_0)$, and let $D$ be a Mumford tower for these data, i.e. a system of schemes $Z_m$ over $\mathrm{Spec}(\mathcal O/\pi^{m+1})$ with transition maps, properness and flatness over the base, finite sets contained in affine opens, charts, and a family of morphisms $q_m$ attaching to every $\mathcal O$-algebra $B$ with $\pi^{m+1}=0$ in $B$ and every Deligne datum $P$ over $B$ (a choice of $B$-submodule $\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$ for each full lattice $M$ in $K_0^2$, with invertible quotient, compatible with inclusions of lattices and with homotheties, and nondegenerate at every prime of $B$) a morphism $q_m(P) : \mathrm{Spec}\,B \to Z_m$, natural in $B$, compatible with the transition maps and invariant for the $N$-action. Fix a level $n$, an $\mathcal O$-algebra $C$ with $(\pi)^{n+1}=0$ in $C$, a scheme $X'$ with morphisms $p_1 : X' \to Z_n$, $p_2 : X' \to \mathrm{Spec}\,C$ and a morphism $s : \mathrm{Spec}\,C \to \mathrm{Spec}(\mathcal O/\pi^{n+1})$ whose composite with $\mathrm{Spec}$ of $\mathcal O \to \mathcal O/\pi^{n+1}$ is the structure morphism $\mathrm{Spec}\,C \to \mathrm{Spec}\,\mathcal O$, such that $(p_1,p_2)$ exhibits $X'$ as the pullback of the structure morphism $Z_n \to \mathrm{Spec}(\mathcal O/\pi^{n+1})$ along $s$. Let $T$ be a scheme and let $\rho$ assign to every $\mathcal O$-algebra $B$ with $(\pi)^{n+1}=0$ in $B$, every $\mathcal O$-algebra map $c : C \to B$ and every Deligne datum $P$ over $B$ a morphism $\rho_B(c,P) : \mathrm{Spec}\,B \to T$, subject to: naturality, $\rho_{B'}(\varphi \circ c, \varphi_* P) = \rho_B(c,P) \circ \mathrm{Spec}(\varphi)$ for every $\mathcal O$-algebra map $\varphi : B \to B'$ with $B'$ also killed by $\pi^{n+1}$; and $N$-invariance, $\rho_B(c,P') = \rho_B(c,P)$ whenever $g \in \mathrm{GL}_2(K_0)$ has class in $N$ and $P'$ is obtained from $P$ by $g^{-1}$, in the sense that $P'.\mathrm{line}(M)$ is the preimage of $P.\mathrm{line}(g^{-1}M)$ under the base-changed action isomorphism for every full lattice $M$. Then for every $\mathcal O$-algebra $B$ with $(\pi)^{n+1}=0$ in $B$, every $c : C \to B$ and all Deligne data $P, P'$ over $B$ with $q_n(P) = q_n(P')$ one has $\rho_B(c,P) = \rho_B(c,P')$.
--
--   This is the separatedness half of the descent of a natural, $N$-invariant family $\rho$ of morphisms to $T$ through the moduli map $q_n$ of a Mumford tower: two Deligne data with the same image under $q_n$ receive the same value. It is used in the construction of a morphism $X' \to T$ compatible with $\rho$ in [`CerednikDrinfeld.FormalOmega.MumfordTower.exists_hom_pullback_of_natural_of_invariant`](thm.html#CerednikDrinfeld.FormalOmega.MumfordTower.exists_hom_pullback_of_natural_of_invariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordTower_eq_of_q_eq_of_natural_of_invariant.lean

import Definitions.Def_CerednikDrinfeld_MumfordTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.eq_of_q_eq_of_natural_of_invariant
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
      ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → ρ B hB c P' = ρ B hB c P)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : C →ₐ[𝒪] B)
    (P P' : (Omega K₀ π).obj B) (hq : D.q n B hB P = D.q n B hB P') :
    ρ B hB c P = ρ B hB c P' := by sorry
