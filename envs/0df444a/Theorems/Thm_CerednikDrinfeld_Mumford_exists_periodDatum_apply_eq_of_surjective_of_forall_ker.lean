-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker
-- name    : CerednikDrinfeld.Mumford.exists_periodDatum_apply_eq_of_surjective_of_forall_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/316f28fd-8253-5382-af6d-c61456f364a5
-- title:
--   Descending a symmetric pairing to a period datum
-- statement:
--   Let $E$ be a finite type, $V$ a type with decidable equality, and $D$ a degeneracy datum on $(E,V)$, that is, maps $a,b\colon E\to V$ together with positive integer weights $w\colon E\to\mathbb{N}^{+}$; write $Z(D)=$ `ribbonKernel D` for the submodule of $E\to\mathbb{Z}$ consisting of the functions annihilated by both pushforwards, along $a$ and along $b$, into $V\to\mathbb{Z}$. Let $G$ be a group and $\Phi\colon \mathrm{Additive}(G^{\mathrm{ab}})\to Z(D)$ a surjective homomorphism of additive groups. Let $F\subseteq L$ be fields ($L$ an $F$-algebra) and $\mathrm{ord}\colon \mathrm{Additive}(F^{\times})\to\mathbb{Z}$ a homomorphism. Let $Q_h\colon G\to\operatorname{Hom}(G,F^{\times})$ be bimultiplicative, assumed symmetric, $Q_h(\alpha,\beta)=Q_h(\beta,\alpha)$, trivial on the kernel of $\Phi$ in the sense that $\Phi(\bar\alpha)=0$ implies $Q_h(\alpha,\beta)=1$ for all $\beta$, and satisfying the order law $\mathrm{ord}\,Q_h(\alpha,\beta)=\sum_{e\in E} w(e)\,\Phi(\bar\alpha)_e\,\Phi(\bar\beta)_e$. Then there exists a period datum $P$ for $D$ over $(F,L,\mathrm{ord})$ — a $\mathbb{Z}$-bilinear map $P.Q\colon Z(D)\times Z(D)\to \mathrm{Additive}(F^{\times})$ that is symmetric and satisfies $\mathrm{ord}(P.Q(x,y))=\sum_e w(e)\,x_e y_e$ — such that $P.Q(\Phi(\bar\alpha),\Phi(\bar\beta))=Q_h(\alpha,\beta)$ for all $\alpha,\beta\in G$.
--
--   This is the descent step in the Mumford–Manin–Drinfeld period formalism: a symmetric bimultiplicative period pairing defined on a group $G$ acting on a tree, killed by the classes mapping to zero in the ribbon kernel of the degeneracy datum, is transported to a period datum indexed by the edges and vertices of the quotient graph. It is used by [`AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient`](thm.html#AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient) to produce the period datum attached to a Mumford quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.GroupTheory.Abelianization.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.Mumford.exists_periodDatum_apply_eq_of_surjective_of_forall_ker
    {E V : Type} [Fintype E] [DecidableEq V] (D : CerednikDrinfeld.DegeneracyData E V)
    {G : Type} [Group G] (Φ : Additive (Abelianization G) →+ ↥(CerednikDrinfeld.ribbonKernel D))
    (hΦ : Function.Surjective Φ)
    (F L : Type) [Field F] [Field L] [Algebra F L] (ord : Additive Fˣ →+ ℤ)
    (Qh : G →* G →* Fˣ) (hsymm : ∀ α β : G, Qh α β = Qh β α)
    (hker : ∀ α : G, Φ (Additive.ofMul (Abelianization.of α)) = 0 → ∀ β : G, Qh α β = 1)
    (hord : ∀ α β : G, ord (Additive.ofMul (Qh α β)) =
      ∑ e : E, (D.w e : ℤ) * ((Φ (Additive.ofMul (Abelianization.of α)) : E → ℤ) e *
                              (Φ (Additive.ofMul (Abelianization.of β)) : E → ℤ) e)) :
    ∃ P : CerednikDrinfeld.Mumford.PeriodDatum D F L ord,
      ∀ α β : G, P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))) =
        Additive.ofMul (Qh α β) := by sorry
