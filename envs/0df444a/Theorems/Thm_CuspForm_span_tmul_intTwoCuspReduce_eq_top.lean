-- Prove2me | Theorems.Thm_CuspForm_span_tmul_intTwoCuspReduce_eq_top
-- name    : CuspForm.span_tmul_intTwoCuspReduce_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/9eb7e1ee-c3f9-57c9-a67e-0ba916d1a348
-- title:
--   Pure tensors 1⊗̄ f span the base change
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number and $H$ a subgroup of $(\mathbb{Z}/M)^{\times}$, and let $K$ be a field equipped with an algebra structure over $\mathbb{Z}/p$. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, i.e. the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the character $\Gamma_0(M)\to(\mathbb{Z}/M)^{\times}$ sending $\gamma$ to its lower right entry mod $M$. Call a cusp form $f\in S_2(\Gamma_H(M))$ two-cusp integral (membership in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54)) when for every $t$ in the Hecke subring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ for $(M,p)$ — a factorisation $M=pR$ together with integers $a,b$ satisfying $pa-Rb=1$ — and every $n$, the $n$-th $q$-expansion coefficient of $t f$ and that of $(t f)\mid_{2}W$ both lie in the prime subring $\bot\subseteq\mathbb{C}$. Let $L=$ `twoCuspLattice M H 2 p ⊥` be the $\bot$-span of this set, and let $\bar L=$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) be the quotient of $L$ by $p\cdot L$, with $f\mapsto\bar f$ the quotient map `intTwoCuspReduce`. The assertion is that the $K$-submodule of $K\otimes_{\mathbb{Z}/p}\bar L$ spanned by the pure tensors $1\otimes\bar f$, as $f$ runs over the two-cusp integral forms, is everything.
--
--   This is the generation statement underlying the two-cusp $q$-expansion principle: a $K$-linear map out of $K\otimes_{\mathbb{Z}/p}\bar L$ is determined by its values on the tensors $1\otimes\bar f$ with $f$ two-cusp integral. It is used in the comparison of $K\otimes_{\mathbb{Z}/p}\bar L$ with regular differentials on the modular curve, namely by [`ModularCurve.exists_linearEquiv_intTwoCuspForms_twoCompRegularDifferentials`](thm.html#ModularCurve.exists_linearEquiv_intTwoCuspForms_twoCompRegularDifferentials) and by the resulting equality of ranks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_span_tmul_intTwoCuspReduce_eq_top.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.span_tmul_intTwoCuspReduce_eq_top
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (K : Type*) [Field K] [Algebra (ZMod p) K] :
    Submodule.span K {x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩} = ⊤ := by sorry
