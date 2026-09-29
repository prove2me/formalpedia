-- Prove2me | Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_gammaH
-- name    : CohCarrier.exists_eichlerShimura_H1_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/fb232bb1-8368-5938-ab47-ed1341bab3fe
-- title:
--   Hecke-equivariant weight-two Eichler–Shimura isomorphism for Γ_H(M)
-- statement:
--   Let $M \ge 1$ and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$; write $\Gamma = \Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$ consisting of the matrices of $\Gamma_0(M)$ whose lower-right entry, reduced mod $M$, lies in $H$, and write $H^1 =$ [`CohCarrier.H1 M H ℂ`](def/CohCarrier_Level.html#L162) for the $\mathbb{C}$-module of additive homomorphisms $\mathrm{Additive}\,\Gamma \to \mathbb{C}$, i.e. of group homomorphisms $\Gamma \to \mathbb{C}$. The assertion is that there exist a monoid endomorphism $J$ of $\Gamma$ and a $\mathbb{C}$-linear map $ES \colon S_2(\Gamma) \times S_2(\Gamma) \to H^1$ (weight-$2$ cusp forms for $\Gamma$ in each factor) with the following properties. First, for every $\gamma \in \Gamma$ the image of $J\gamma$ in $\mathrm{SL}(2,\mathbb{Z})$ is [`ModularCurve.Period.jConjSL`](def/ModularCurve_PeriodHomPair.html#L47) applied to $\gamma$, the conjugation by $\mathrm{diag}(1,-1)$. Second, for all $f, g$ and all $\gamma \in \Gamma$, $$ES(f,g)(\gamma) = P(f)(\gamma) + P(f)(J\gamma) + P(g)(\gamma) - P(g)(J\gamma),$$ where $P(f) =$ [`ModularCurve.periodMapOf Γ f`](def/ModularCurve_PeriodOf.html#L79) is the period homomorphism attached to an equivariant primitive of $f$ (and $0$ if none exists). Third, $ES$ is injective. Fourth, the range of $ES$ is exactly [`ModularCurve.Period.parabolicHoms ℂ Γ ℂ`](def/ModularCurve_PeriodMap.html#L62), the submodule of homomorphisms $\Gamma \to \mathbb{C}$ satisfying `IsParabolicHom`. Finally, $ES$ intertwines the operators on forms with those on $H^1$: for every prime $\ell \nmid M$, $ES(T_\ell f, T_\ell g) =$ [`CohCarrier.heckeT M H ℓ ℂ`](def/CohCarrier_Level.html#L250) $(ES(f,g))$; for every prime $q \mid M$, $ES(U_q f, U_q g) =$ [`CohCarrier.heckeT M H q ℂ`](def/CohCarrier_Level.html#L250) $(ES(f,g))$ — the same transfer operator on the cohomological side; and for every $d \in (\mathbb{Z}/M)^\times$, $ES(\langle d\rangle f, \langle d\rangle g) =$ [`CohCarrier.diamondL M H ℂ d`](def/CohCarrier_Inst.html#L55) $(ES(f,g))$, the operator given by precomposition with conjugation by a chosen element of $\Gamma_0(M)$ with lower-right entry $d$. Here $T_\ell$, $U_q$, $\langle d\rangle$ on forms are [`CuspForm.heckeTLinH 2`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224), [`CuspForm.heckeULinH 2`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171), [`CuspForm.diamondLinH 2`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), each defined as the corresponding weight-$2$ operator when the relevant stability predicate (`StableT`, `StableU`, `StableD`) holds and as $0$ otherwise.
--
--   This is the Eichler–Shimura isomorphism in weight $2$ for $\Gamma_H(M)$, in the form of an explicit $\mathbb{C}$-linear bijection from pairs of cusp forms (holomorphic and antiholomorphic parts) onto parabolic cohomology, compatible with the Hecke operators $T_\ell$, the operators $U_q$ at primes dividing the level, and the diamond operators. It is the source of Hecke eigenvectors in parabolic cohomology used downstream, for instance in the construction of eigenforms attached to eigenclasses and in the statements about primitive classes with prescribed $T_\ell$-eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_eichlerShimura_H1_gammaH.lean

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_eichlerShimura_H1_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ (J : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
      (ES : (CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2)
        →ₗ[ℂ] CohCarrier.H1 M H ℂ),
      (∀ γ : ↥(CohCarrier.GammaH M H), ((J γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
        ModularCurve.Period.jConjSL (γ : SL(2, ℤ))) ∧
      (∀ (f g : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)),
        ES (f, g) (Additive.ofMul γ) =
          ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul γ) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul (J γ)) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul γ) -
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul (J γ))) ∧
      Function.Injective ES ∧
      LinearMap.range ES = ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ES (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) =
          CohCarrier.heckeT M H ℓ ℂ (ES (f, g))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero q := ⟨hq.ne_zero⟩
        ES (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) =
          CohCarrier.heckeT M H q ℂ (ES (f, g))) ∧
      (∀ (d : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        ES (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) =
          CohCarrier.diamondL M H ℂ d (ES (f, g))) := by sorry
