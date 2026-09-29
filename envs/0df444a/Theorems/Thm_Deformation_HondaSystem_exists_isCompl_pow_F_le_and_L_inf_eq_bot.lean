-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_isCompl_pow_F_le_and_L_inf_eq_bot
-- name    : Deformation.HondaSystem.exists_isCompl_pow_F_le_and_L_inf_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/cab5bfb0-571b-51ec-a30f-aedf78301ae7
-- title:
--   Connected–étale splitting of a free Honda system
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime whose image in $\mathcal O$ is a non-zero-divisor, equipped with an $\mathcal O$-algebra structure on $\mathbb Z/p$ whose structure map has kernel exactly the ideal $(p)$, and assume $\mathcal O$ is $(p)$-adically complete (in Mathlib's sense: Hausdorff and precomplete for the $(p)$-adic filtration). Let $r\in\mathbb N$ and let $H_1$ be a Honda system with parameter $p$ on the free module $\mathcal O^r=(\mathrm{Fin}\ r\to\mathcal O)$, i.e. $\mathcal O$-linear endomorphisms $F,V$ with $F\circ V=V\circ F=p\cdot\mathrm{id}$ together with a submodule $L$ satisfying: every $x\in L$ lying in $\operatorname{range} F$ is of the form $p\,y$ with $y\in L$; $p\,y\in\operatorname{range} F$ for all $y\in L$; $\operatorname{range}F+L$ is everything; and $V$ is injective on $L$. The assertion is the existence of complementary submodules $M^c,M^{\text{ét}}$ of $\mathcal O^r$ (an `IsCompl` pair) such that: both are stable under $F$ and under $V$; there is an $N$ with $F^N m\in p\,M^c$ for all $m\in M^c$ (the witness being taken in $M^c$); $F$ maps $M^{\text{ét}}$ onto $M^{\text{ét}}$ and $M^{\text{ét}}\subseteq\operatorname{range}F$; $m\in M^{\text{ét}}$ if and only if $m\in F^N(\mathcal O^r)$ for every $N$; $m\in M^c$ if and only if for every $k$ there is an $N$ with $F^N m\in p^k\mathcal O^r$; both $M^c$ and $M^{\text{ét}}$ are free with $\operatorname{rank}M^c+\operatorname{rank}M^{\text{ét}}=r$; $L\cap M^{\text{ét}}=0$; and, writing $L^c$ for the image of $L$ under the projection onto $M^c$ along $M^{\text{ét}}$ (viewed inside $\mathcal O^r$), the three Honda conditions again hold for $L^c$: every element of $L^c\cap\operatorname{range}F$ is $p$ times an element of $L^c$, $p\,L^c\subseteq\operatorname{range}F$, and $\operatorname{range}F+L^c$ is everything.
--
--   Classically this is the Dieudonné-module form of the connected–étale decomposition of a finite or $p$-divisible commutative group over $\mathbb F_p$, as in Fontaine's treatment of Honda systems: étale corresponds to $F$ bijective, connected to $F$ topologically nilpotent, and the Hodge submodule $L$ meets the étale part trivially. Compared with the textbook statement, the formal version asserts existence only (no uniqueness), records the two pieces by the explicit divisibility criteria $M^{\text{ét}}=\bigcap_N F^N(\mathcal O^r)$ and $M^c=\{m:\ F^N m\to 0\ p\text{-adically}\}$, and adds that the projection $L^c$ of $L$ into the connected part again satisfies the Honda conditions on $L$. It feeds the construction of split coordinates in normal form for a Honda system matched with a compatible system of Dieudonné modules of finite Hopf algebras over $\mathbb Z/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_isCompl_pow_F_le_and_L_inf_eq_bot.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Deformation.HondaSystem.exists_isCompl_pow_F_le_and_L_inf_eq_bot
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)) :
    ∃ (Mc Met : Submodule 𝓞 (Fin r → 𝓞)) (hc : IsCompl Mc Met),

      (∀ m ∈ Mc, H₁.F m ∈ Mc ∧ H₁.V m ∈ Mc) ∧ (∀ m ∈ Met, H₁.F m ∈ Met ∧ H₁.V m ∈ Met) ∧

      (∃ N : ℕ, ∀ m ∈ Mc, ∃ y ∈ Mc, (H₁.F ^ N) m = (p : 𝓞) • y) ∧
      (∀ m ∈ Met, ∃ m' ∈ Met, H₁.F m' = m) ∧ Met ≤ LinearMap.range H₁.F ∧

      (∀ m, m ∈ Met ↔ ∀ N : ℕ, ∃ y, (H₁.F ^ N) y = m) ∧
      (∀ m, m ∈ Mc ↔ ∀ k : ℕ, ∃ N : ℕ, ∃ y, (H₁.F ^ N) m = (p : 𝓞) ^ k • y) ∧

      Module.Free 𝓞 Mc ∧ Module.Free 𝓞 Met ∧ Module.finrank 𝓞 Mc + Module.finrank 𝓞 Met = r ∧

      H₁.L ⊓ Met = ⊥ ∧

      (∀ x ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc),
        x ∈ LinearMap.range H₁.F →
          ∃ y ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc), x = (p : 𝓞) • y) ∧
      (∀ y ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc),
        (p : 𝓞) • y ∈ LinearMap.range H₁.F) ∧
      LinearMap.range H₁.F ⊔ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc) = ⊤ := by sorry
