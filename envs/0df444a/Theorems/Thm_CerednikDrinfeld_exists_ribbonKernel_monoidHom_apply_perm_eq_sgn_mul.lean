-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_ribbonKernel_monoidHom_apply_perm_eq_sgn_mul
-- name    : CerednikDrinfeld.exists_ribbonKernel_monoidHom_apply_perm_eq_sgn_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/abccf3b0-44e9-55e4-8ad0-1cb3989666cb
-- title:
--   Signed permutation action on a ribbon kernel by isometries
-- statement:
--   Let $E$ and $V$ be types with $E$ finite (and decidable equality on $E$ and $V$), and let $D$ be a `DegeneracyData E V`, that is a pair of maps $a, b : E \to V$ together with a width function $w : E \to \mathbb{N}^{+}$. Write $\mathrm{pushforward}\,f$ for the $\mathbb{Z}$-linear map $(E \to \mathbb{Z}) \to (V \to \mathbb{Z})$ sending $x$ to $v \mapsto \sum_{e} [f(e) = v]\, x(e)$; then `ribbonKernel D` is the submodule $\ker(\mathrm{pushforward}\,D.a) \cap \ker(\mathrm{pushforward}\,D.b)$ of $E \to \mathbb{Z}$ (the intersection over $i \in \mathrm{Fin}\,2$ of the kernels of `jointDelta D i`), and `ribbonGram D` is the restriction to it of the pairing $\langle x, y\rangle = \sum_{e} w(e)\, x(e)\, y(e)$, viewed as a map into the $\mathbb{Z}$-dual. Let $S$ be a group with homomorphisms $\pi_V : S \to \mathrm{Perm}(V)$, $\pi_E : S \to \mathrm{Perm}(E)$ and $\mathrm{sgn} : S \to \mathbb{Z}^{\times}$, and assume: $w(\pi_E(\sigma)e) = w(e)$ for all $\sigma, e$; whenever $\mathrm{sgn}(\sigma) = 1$, $a(\pi_E(\sigma)e) = \pi_V(\sigma)(a(e))$ and $b(\pi_E(\sigma)e) = \pi_V(\sigma)(b(e))$; and whenever $\mathrm{sgn}(\sigma) = -1$, $a(\pi_E(\sigma)e) = \pi_V(\sigma)(b(e))$ and $b(\pi_E(\sigma)e) = \pi_V(\sigma)(a(e))$. The conclusion asserts the existence of a group homomorphism $\mathrm{actZ}$ from $S$ to the $\mathbb{Z}$-linear automorphisms of `ribbonKernel D` such that for all $\sigma \in S$, $x$ in the ribbon kernel and $e \in E$ one has $(\mathrm{actZ}(\sigma)x)(\pi_E(\sigma)e) = \mathrm{sgn}(\sigma)\, x(e)$, and such that each $\mathrm{actZ}(\sigma)$ preserves the width pairing: $\langle \mathrm{actZ}(\sigma)x, \mathrm{actZ}(\sigma)y\rangle = \langle x, y\rangle$ for all $x, y$.
--
--   The ribbon kernel is the cycle lattice of the weighted bipartite graph encoded by $(a, b, w)$, the combinatorial model of the character group of the toric part of a semistable degeneration with its monodromy pairing; the theorem realises a group of symmetries of the graph that may exchange the two sides of the bipartition as a group of isometries, by signed relabelling of edge-indexed divisors. It is used in the Čerednik–Drinfeld part of the formalisation, for instance by the statements producing permutation realisations on quotient vertex and edge sets and the quotient presentation of the class set with its Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_ribbonKernel_monoidHom_apply_perm_eq_sgn_mul.lean

import Definitions.Def_CerednikDrinfeld_Ribbon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.exists_ribbonKernel_monoidHom_apply_perm_eq_sgn_mul
    {E V : Type} [Fintype E] [DecidableEq E] [DecidableEq V] (D : DegeneracyData E V)
    {S : Type} [Group S] (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hw : ∀ (σ : S) (e : E), D.w (πE σ e) = D.w e)
    (hsame : ∀ (σ : S) (e : E), sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hswap : ∀ (σ : S) (e : E), sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e)) :
    ∃ actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)),
      (∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E),
        (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e) ∧
      (∀ (σ : S) (x y : ↥(ribbonKernel D)), ribbonGram D (actZ σ x) (actZ σ y) = ribbonGram D x y) := by sorry
