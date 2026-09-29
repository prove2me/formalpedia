-- Prove2me | Theorems.Thm_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span
-- name    : CuspForm.exists_linearIndependent_forall_twoCuspLattice_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/70c8c275-93cb-5b82-899d-96e2f20fdda3
-- title:
--   Two-cusp lattice at p ‖ M has a coefficient-independent basis
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^{2} \nmid M$, and let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$ such that every unit $u$ of $\mathbb{Z}/M$ whose image under the map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ induced by $M/p \mid M$ equals $1$ lies in $H$. Write $\Gamma_{H}(M)$ for the congruence subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$, namely the image in $\mathrm{SL}(2,\mathbb{Z})$ of the set of $\gamma \in \Gamma_{0}(M)$ whose lower-right entry, reduced mod $M$, lies in $H$. Then there are a natural number $n$ and a family $b : \mathrm{Fin}\,n \to \mathrm{CuspForm}(\Gamma_{H}(M), 2)$ of weight-two cusp forms which is linearly independent over $\mathbb{C}$ and whose $\mathbb{C}$-span is all of $\mathrm{CuspForm}(\Gamma_{H}(M), 2)$, and which has the further property that for *every* subring $A \subseteq \mathbb{C}$ the submodule [`CuspForm.twoCuspLattice M H 2 p A`](def/CuspForm_TwoCuspLattice.html#L86) coincides with the $A$-span of the range of $b$. Here `twoCuspLattice M H 2 p A` is the $A$-span of the set of those $f$ for which, for every $t$ in the Hecke ring [`CuspForm.heckeRingH M H 2`](def/CuspForm_TwoCuspLattice.html#L37), every Atkin–Lehner datum $W$ of [`ModularForm.AtkinLehnerDatum M p`](def/ModularForm_AtkinLehnerDatum.html#L14), and every $n \in \mathbb{N}$, the $n$-th $q$-expansion coefficient of $t f$ and the $n$-th $q$-expansion coefficient of the weight-two slash $W$-transform [`ModularForm.alSlash W 2 (t f)`](def/ModularForm_AtkinLehnerDatum.html#L141) both lie in $A$.
--
--   This is the rationality-and-integrality statement for weight-two cusp forms on $\Gamma_H(M)$ at a prime exactly dividing the level: the two-cusp integral lattice, cut out by integrality of Hecke translates both at $\infty$ and after slashing by the Atkin–Lehner involutions at $p$, is free with a single basis valid simultaneously for all coefficient rings $A \subseteq \mathbb{C}$, so that in particular it is a full lattice over $\mathbb{Z}$ and $L_A$ is obtained from $L_{\mathbb{Z}}$ by base change. It underlies the later comparison of the lattice with integral $q$-expansions and with differentials, and the construction of the Hecke-equivariant integral structures used in the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_linearIndependent_forall_twoCuspLattice_eq_span
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    ∃ (n : ℕ) (b : Fin n → CuspForm (CohCarrier.GammaH M H) 2),
      LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ ∧
        ∀ A : Subring ℂ, CuspForm.twoCuspLattice M H 2 p A = Submodule.span A (Set.range b) := by sorry
