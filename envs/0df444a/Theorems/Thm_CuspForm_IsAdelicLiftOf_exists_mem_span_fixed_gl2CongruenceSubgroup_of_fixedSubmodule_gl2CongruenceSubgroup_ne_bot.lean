-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_gl2CongruenceSubgroup_of_fixedSubmodule_gl2CongruenceSubgroup_ne_bot
-- name    : CuspForm.IsAdelicLiftOf.exists_mem_span_fixed_gl2CongruenceSubgroup_of_fixedSubmodule_gl2CongruenceSubgroup_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/0b0d9db6-c088-5acb-b1df-fc8f0f6b5ad0
-- title:
--   Central K(qⁿ)-fixed vector in the local span of an adelic lift
-- statement:
--   Let $M$ be a nonzero natural number, let $g$ be a cusp form of weight $2$ on $\Gamma_0(M)$, and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ which is an adelic lift of $g$ in the sense that: $\Phi$ is invariant under left multiplication by the image of $\mathrm{GL}_2(\mathbb{Q})$; $\Phi$ is invariant under right multiplication by the image, under the embedding of the finite-adelic $\mathrm{GL}_2$, of the subgroup `finiteLevelOne` attached to the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$; and for every adelic matrix $h$ whose finite component is trivial and whose real component lies in $\mathrm{GL}_2^{+}(\mathbb{R})$, the value $\Phi(h)$ is the weight-$2$ slash of $g$ by that real component, evaluated at $i$. Let $q$ be a prime and $n$ a natural number, and write $K(q^n)$ for the subgroup of $\mathrm{GL}_2(\mathbb{Q}_q)$ consisting of those $x$ with $\lVert (x-1)_{ij}\rVert \le q^{-n}$ and $\lVert (x^{-1}-1)_{ij}\rVert \le q^{-n}$ for all $i,j$. Let $V_\Phi$ denote the adelic span of $\Phi$, namely the complex span inside the space of functions on adelic $\mathrm{GL}_2$ of all translates $h \cdot \Phi$ by adelic matrices $h$, and assume that the submodule of $K(q^n)$-fixed vectors of $V_\Phi$ is non-zero. Then there exists $y \in V_\Phi$ which lies in the complex span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of $\Phi$ itself, is non-zero, is fixed by every element of $K(q^n)$, and satisfies $z \cdot y = y$ for every $z \in \mathbb{Q}_q^{\times}$ acting through the central embedding $z \mapsto z \cdot 1$ into $\mathrm{GL}_2(\mathbb{Q}_q)$.
--
--   This is the descent, for the principal congruence subgroups $K(q^n)$, from a fixed vector in the full adelic span of an adelic lift to a non-zero vector in the span of the local $\mathrm{GL}_2(\mathbb{Q}_q)$-translates which is simultaneously $K(q^n)$-fixed and fixed by the centre, in the style of the adelization of classical newform theory. It feeds the statements extracting cuspidal automorphic data and non-zero linear forms on the local representation space attached to a newform, used in the modularity-lifting and level-lowering inputs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_exists_mem_span_fixed_gl2CongruenceSubgroup_of_fixedSubmodule_gl2CongruenceSubgroup_ne_bot.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ConductorDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.exists_mem_span_fixed_gl2CongruenceSubgroup_of_fixedSubmodule_gl2CongruenceSubgroup_ne_bot
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (n : ℕ)
    (hfix : LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n) (LocalNewvector.AdelicSpan Φ) ≠ ⊥) :
    ∃ y : LocalNewvector.AdelicSpan Φ,
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n) (LocalNewvector.AdelicSpan Φ) ∧
      ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y = y := by sorry
