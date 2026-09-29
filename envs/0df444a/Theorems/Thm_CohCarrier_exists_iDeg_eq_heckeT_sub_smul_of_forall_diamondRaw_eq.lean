-- Prove2me | Theorems.Thm_CohCarrier_exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq
-- name    : CohCarrier.exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6a7a686e-0b1e-547f-bcd4-784215335ab1
-- title:
--   Hecke operator acts by its degree on diamond-invariant classes
-- statement:
--   Fix $L \ge 1$ and an additive commutative group $A$, and let $H, H'$ be subgroups of $(\mathbb{Z}/L\mathbb{Z})^\times$. The hypothesis `h : CohCarrier.LevelLE L L H' H 1` records that $L \mid L$, that $1 \mid 1$, and that every unit of $\mathbb{Z}/L\mathbb{Z}$ lying in $H$ has its reduction in $H'$, i.e. $H \le H'$. Assume that multiplication by $H.\mathrm{relIndex}\,H' = [H' : H \cap H']$ is injective on $A$: if $[H' : H\cap H']\cdot a = 0$ then $a = 0$. Let $\ell$ be a prime with $\ell \nmid L$. For a subgroup $K \le (\mathbb{Z}/L\mathbb{Z})^\times$, [`CohCarrier.GammaH L K`](def/CohCarrier_Level.html#L133) is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the elements of $\Gamma_0(L)$ whose lower-right entry reduces into $K$, and [`CohCarrier.H1 L K A`](def/CohCarrier_Level.html#L162) is the group of additive homomorphisms $\mathrm{Additive}\,\Gamma_K(L) \to A$, i.e. homomorphisms $\Gamma_K(L) \to A$ with $A$ a trivial module. Let $\varphi \in$ [`CohCarrier.H1 L H A`](def/CohCarrier_Level.html#L162) satisfy: for every $\sigma \in \Gamma_0(L)$ whose matrix lies in $\Gamma_{H'}(L)$, one has $\varphi \circ (\gamma \mapsto \sigma\gamma\sigma^{-1}) = \varphi$ on $\Gamma_H(L)$ (the diamond action `diamondRaw` fixes $\varphi$). Then there exists $\psi \in$ [`CohCarrier.H1 L H' A`](def/CohCarrier_Level.html#L162), a homomorphism $\Gamma_{H'}(L) \to A$, whose image under [`CohCarrier.iDeg' L L H' H 1 A h`](def/CohCarrier_Level.html#L396), namely precomposition with `iotaDeg L L H' H 1 h` $: \Gamma_H(L) \to \Gamma_{H'}(L)$, $\gamma \mapsto$ `conjLowerMat 1 γ`, equals $T_\ell\varphi - (\ell+1)\varphi$; here $T_\ell =$ [`CohCarrier.heckeT L H ℓ A`](def/CohCarrier_Level.html#L250) is the transfer to $\Gamma_H(L)$ of the composition of $\varphi$ with the conjugation homomorphism `conjL L H ℓ` from `GammaHUpper L H ℓ`.
--
--   This is the statement that on diamond-invariant classes modulo those restricted from the larger level, the Hecke operator $T_\ell$ for $\ell \nmid L$ acts through its degree $\ell + 1$ — the Eisenstein property of the transgression classes of the covering $\Gamma_H(L) \trianglelefteq \Gamma_{H'}(L)$. The proof uses the transfer–restriction identity, the index computation $[\Gamma_H(L) : \Gamma_H(L)\cap\Gamma^0(\ell)] = \ell+1$ and the commutation of $T_\ell$ with the level map; it feeds the rank computation for the corner submodule of $H^1$ in the non-Eisenstein case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq
    (L : ℕ) [NeZero L] (A : Type) [AddCommGroup A]
    (H H' : Subgroup (ZMod L)ˣ) (h : CohCarrier.LevelLE L L H' H 1)
    (hA : ∀ a : A, H.relIndex H' • a = 0 → a = 0)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L)
    (φ : CohCarrier.H1 L H A)
    (hφ : ∀ σ : ↥(CongruenceSubgroup.Gamma0 L), (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH L H' →
      CohCarrier.diamondRaw L H A σ φ = φ) :
    ∃ ψ : CohCarrier.H1 L H' A,
      CohCarrier.iDeg' L L H' H 1 A h ψ = CohCarrier.heckeT L H ℓ A φ - (ℓ + 1) • φ := by sorry
