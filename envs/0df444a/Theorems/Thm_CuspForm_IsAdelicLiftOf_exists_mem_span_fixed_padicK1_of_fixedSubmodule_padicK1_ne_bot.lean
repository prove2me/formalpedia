-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot
-- name    : CuspForm.IsAdelicLiftOf.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/66d19f9a-c149-538e-9f09-25e215c03099
-- title:
--   Central K₁(qᵃ)-fixed vector inside the GL₂(ℚ_q)-span
-- statement:
--   Let $M$ be a nonzero natural number, $g$ a weight-two cusp form for $\Gamma_0(M)$, and $\Phi$ a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ which is an adelic lift of $g$, meaning: $\Phi$ is invariant under left multiplication by the image of $\mathrm{GL}_2(\mathbb{Q})$ under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), invariant under right multiplication by the image under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of the subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418) attached to the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$, and satisfies $\Phi(h) = (g \mid_2 \mathrm{ratArchGL2}\,h)(i)$ for every $h$ whose finite component `glFin` is trivial and whose real component `ratArchGL2` has positive determinant. Let $q$ be a prime and $a$ a natural number. Write $V$ for [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$, the $\mathbb{C}$-span of all right translates $h \cdot \Phi$, $h \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and let $K_1(q^a) \subseteq \mathrm{GL}_2(\mathbb{Q}_q)$ be [`LocalNewvector.padicK1 q a`](def/LocalNewvector_CongruenceSubgroupK1.html#L161): those elements coming from a matrix in $\mathrm{GL}_2(\mathbb{Z}_q)$ with $(1,0)$-entry in $(q^a)$ and $(1,1)$-entry congruent to $1$ modulo $q^a$. Assume the submodule of $K_1(q^a)$-fixed vectors of $V$ is nonzero. Then there is $y \in V$ lying in the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-orbit of [`LocalNewvector.AdelicSpan.self`](def/LocalNewvector_AdelicSpanCarrier.html#L121) $\Phi$ (the vector $\Phi$ itself) with $y \neq 0$, $y$ fixed by every element of $K_1(q^a)$, and $z \cdot y = y$ for every $z \in \mathbb{Q}_q^{\times}$ acting through the scalar embedding [`LocalNewvector.centralGL`](def/LocalNewvector_ConductorDatum.html#L64).
--
--   This transfers a $K_1(q^a)$-fixed vector from the full adelic span of an adelic lift of a weight-two cusp form to the span of the local $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the lift, simultaneously arranging trivial action of the centre — the standard smooth-representation-theoretic step preceding the analysis of newvectors and conductors at $q$. It is used in identifying the local conductor of the adelic span of a newform and in establishing irreducibility of the associated $\mathrm{GL}_2(\mathbb{Q}_q)$-representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ConductorDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (a : ℕ)
    (hfix : LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan Φ) ≠ ⊥) :
    ∃ y : LocalNewvector.AdelicSpan Φ,
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan Φ) ∧
      ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y = y := by sorry
