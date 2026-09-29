-- Prove2me | Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_top
-- name    : CohCarrier.exists_eichlerShimura_H1_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/80750078-a7c3-5ac1-978d-73b1f59d7689
-- title:
--   Hecke-equivariant Eichler–Shimura map into H¹ at H=top
-- statement:
--   Let $N$ be a nonzero natural number. Write $\Gamma_H(N,\top)$ for [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of the full subgroup $\top \le (\mathbb{Z}/N)^\times$ under the determinant-type character $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$, $\gamma \mapsto \gamma_{11} \bmod N$; by [`CohCarrier.GammaH_le_Gamma0`](def/CohCarrier_Level.html#L146) it is contained in $\Gamma_0(N)$, and [`CohCarrier.H1 N ⊤ ℂ`](def/CohCarrier_Level.html#L162) is the space of additive homomorphisms $\mathrm{Additive}\,\Gamma_H(N,\top) \to \mathbb{C}$, i.e. of group homomorphisms $\Gamma_H(N,\top) \to \mathbb{C}$. The assertion is that there is a $\mathbb{C}$-linear map $\mathrm{ES}$ from pairs of weight-two cusp forms on $\Gamma_0(N)$ to [`CohCarrier.H1 N ⊤ ℂ`](def/CohCarrier_Level.html#L162) with five properties: (i) for every pair $(f,g)$ and every $\gamma \in \Gamma_H(N,\top)$, $\mathrm{ES}(f,g)(\gamma)$ equals the value of [`ModularCurve.periodHomPair N (f,g)`](def/ModularCurve_PeriodHomPair.html#L135) at $\gamma$ regarded as an element of $\Gamma_0(N)$, where `periodHomPair` is, once a linear choice `pml` of the period map exists, the map $(f,g) \mapsto (1+\iota^{*})\mathrm{pml}(f) + (1-\iota^{*})\mathrm{pml}(g)$ with $\iota^{*}$ the involution `charInvolution` given by pull-back along conjugation on $\Gamma_0(N)$ (and $0$ otherwise); (ii) $\mathrm{ES}$ is injective; (iii) the range of $\mathrm{ES}$ is [`ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ`](def/ModularCurve_PeriodMap.html#L62), the submodule of those homomorphisms vanishing on every $\gamma$ whose integral matrix has trace squared equal to $4$; (iv) for every prime $\ell \nmid N$ and all $f,g$, $\mathrm{ES}(T_\ell f, T_\ell g) =$ [`CohCarrier.heckeT N ⊤ ℓ ℂ`](def/CohCarrier_Level.html#L250) applied to $\mathrm{ES}(f,g)$, where $T_\ell$ is [`CuspForm.heckeTLin 2`](def/ModularForm_HeckeOperatorForms.html#L69) and [`CohCarrier.heckeT`](def/CohCarrier_Level.html#L250) is the transfer-built operator on $H^1$; (v) likewise for every prime $q \mid N$ with $T_\ell$ replaced by the operator [`CuspForm.heckeULin 2`](def/ModularForm_HeckeOperatorForms.html#L83) on forms, again matched with [`CohCarrier.heckeT N ⊤ q ℂ`](def/CohCarrier_Level.html#L250).
--
--   This is the complex-coefficient Eichler–Shimura isomorphism in weight two, in the Hecke-equivariant form needed on the cohomological carrier $H^1(\Gamma_H(N),\mathbb{C})$ on which the level-raising and patching arguments are formalised: two copies of $S_2(\Gamma_0(N))$ are identified with parabolic cohomology compatibly with $T_\ell$ and $U_q$. It is used by the statements describing parabolic classes with prescribed Hecke eigenvalues and degeneracy-map behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_eichlerShimura_H1_top.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodHomPair
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups in

theorem CohCarrier.exists_eichlerShimura_H1_top (N : ℕ) [NeZero N] :
    ∃ ES : (CuspForm (CongruenceSubgroup.Gamma0 N) 2 × CuspForm (CongruenceSubgroup.Gamma0 N) 2)
        →ₗ[ℂ] CohCarrier.H1 N ⊤ ℂ,
      (∀ (fg : CuspForm (CongruenceSubgroup.Gamma0 N) 2 × CuspForm (CongruenceSubgroup.Gamma0 N) 2)
          (γ : ↥(CohCarrier.GammaH N ⊤)),
        ES fg (Additive.ofMul γ) =
          ModularCurve.periodHomPair N fg
            (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩)) ∧
      Function.Injective ES ∧
      LinearMap.range ES = ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
          (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ES (CuspForm.heckeTLin 2 hℓ hℓN f, CuspForm.heckeTLin 2 hℓ hℓN g) =
          CohCarrier.heckeT N ⊤ ℓ ℂ (ES (f, g))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N)
          (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
        haveI : NeZero q := ⟨hq.ne_zero⟩
        ES (CuspForm.heckeULin 2 hqN f, CuspForm.heckeULin 2 hqN g) =
          CohCarrier.heckeT N ⊤ q ℂ (ES (f, g))) := by sorry
