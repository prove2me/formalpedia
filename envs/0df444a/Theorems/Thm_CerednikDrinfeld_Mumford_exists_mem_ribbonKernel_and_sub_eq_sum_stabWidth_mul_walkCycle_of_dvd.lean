-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
-- name    : CerednikDrinfeld.Mumford.exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/453e0d72-df5d-5fed-8f50-b9dfc533c09a
-- title:
--   Harmonic quasi-invariant potentials give stabiliser-weighted cycles on the quotient graph
-- statement:
--   Let a group $G$ act on a type $W$ and let $\mathcal T$ be a simple graph on $W$ whose adjacency is preserved by the action, with every vertex stabiliser $\mathrm{Stab}_G(w)$ finite. Let $\tau : W \to \mathbb Z/2$ be a $G$-invariant function with $\tau u \neq \tau v$ for adjacent $u,v$. Let $E$ be a finite type, $V$ a type, and $D$ a degeneracy datum on $(E,V)$, consisting of maps $a,b : E \to V$ and widths $w : E \to \mathbb Z_{>0}$; let $eE$ be an equivalence of $E$ with the set of $G$-orbits of darts of $\mathcal T$ whose chosen representative has tail of colour $0$, and $eV$ an equivalence of $V$ with the set of $G$-orbits of $W$, such that for each $e$ the orbit $eV(a\,e)$ is that of the tail and $eV(b\,e)$ that of the head of the representative dart of $eE\,e$. Let $\varphi : W \to \mathbb Z$ be quasi-invariant, i.e. for every $g \in G$ there is $n \in \mathbb Z$ with $\varphi(g \cdot w) = \varphi(w) + n$ for all $w$; harmonic, i.e. $\sum_{x \in S}(\varphi x - \varphi u) = 0$ whenever $S$ is a finite set consisting exactly of the neighbours of $u$; and such that for every dart $d$ the cardinality of $\mathrm{Stab}_G(d)$ divides $\varphi(d_{\mathrm{head}}) - \varphi(d_{\mathrm{tail}})$. Write $\mathrm{sw}(e)$ for the cardinality of the stabiliser of the representative dart of $eE\,e$, normalised to $1$ if that cardinality is $0$. Then there exists $c : E \to \mathbb Z$ such that, first, the jump of $\varphi$ across the representative dart of $eE\,e$ equals $\mathrm{sw}(e)\,c(e)$ for every $e$; second, $c$ lies in the ribbon kernel of $D$, the intersection of the kernels of the two pushforward maps $(E \to \mathbb Z) \to (V \to \mathbb Z)$ along $a$ and along $b$, so that for each vertex of $V$ the sums of $c$ over the edges with given $a$-image, respectively given $b$-image, vanish; and third, for all $u,u' \in W$ and every walk $p$ from $u$ to $u'$ in $\mathcal T$, $$\varphi(u') - \varphi(u) = \sum_{e : E} \mathrm{sw}(e)\, c(e)\, \mathrm{walkCycle}(p)(e),$$ where $\mathrm{walkCycle}(p)(e)$ is the signed count over the darts of $p$ of $+1$ for each dart in the orbit $eE\,e$ and $-1$ for each dart whose reverse lies in that orbit.
--
--   This is the tree-lattice version, with torsion allowed, of the statement that a harmonic quasi-invariant potential on a graph with group action descends to a cycle on the quotient graph; the stabiliser orders appear as the thicknesses of the quotient, in Kurihara's sense, and the cycle condition on the quotient is unweighted. It feeds the construction of the Mumford period pairing, being cited by [`CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (MulAction.stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (φ : W → ℤ) (hφ : ∀ g : G, ∃ n : ℤ, ∀ w : W, φ (g • w) = φ w + n)
    (hharm : ∀ (u : W) (S : Finset W), (∀ x, x ∈ S ↔ 𝒯.Adj u x) → ∑ x ∈ S, (φ x - φ u) = 0)
    (hdiv : ∀ d : 𝒯.Dart, ((Nat.card (MulAction.stabilizer G d) : ℕ) : ℤ) ∣ φ d.snd - φ d.fst) :
    ∃ c : E → ℤ,
      (∀ e : E, φ (eE e).1.out.snd - φ (eE e).1.out.fst = ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e) ∧
      c ∈ ribbonKernel D ∧
      ∀ (u u' : W) (p : 𝒯.Walk u u'),
        φ u' - φ u = ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e * walkCycle 𝒯 (fun e => (eE e).1) p e := by sorry
