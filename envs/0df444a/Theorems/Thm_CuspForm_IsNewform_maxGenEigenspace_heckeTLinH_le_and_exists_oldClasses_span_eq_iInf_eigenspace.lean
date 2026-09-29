-- Prove2me | Theorems.Thm_CuspForm_IsNewform_maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
-- name    : CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/7e3a338f-22c9-5d11-93c5-5c84f157cc32
-- title:
--   Oldform degeneracy basis and semisimplicity of good T_ℓ
-- statement:
--   Fix $N\ge 1$, a finite set $S$ of naturals containing every prime divisor of $N$, a divisor $M_g\mid N$ with $M_g\ge 1$, and a weight-two cusp form $g$ on $\Gamma_0(M_g)$ that is a newform in the sense of [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23): $g$ is a normalised eigenform ($a_1(g)=1$, $a_{mn}(g)=a_m(g)a_n(g)$ for coprime $m,n$, and the usual prime-power recursions according as $p\mid M_g$ or not), and for no proper divisor $M$ of $M_g$ does there exist a normalised eigenform of level $M$ whose $\ell$-th coefficients agree with those of $g$ for all primes $\ell\nmid M_g$. All operators act on weight-two cusp forms for [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133), the preimage in $\Gamma_0(N)$ of the full subgroup of $(\mathbb Z/N)^\times$, with [`CuspForm.heckeTLinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) and [`CuspForm.heckeULinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) the level-$N$ operators $T_\ell$ ($\ell$ prime, $\ell\nmid N$) and $U_q$ (defined as the relevant slash-averaging map when the corresponding stability predicate `StableT`, resp. `StableU`, holds, and as $0$ otherwise). The assertion is twofold. First, for every prime $\ell\nmid N$ and every $\nu\in\mathbb C$ the maximal generalised eigenspace of $T_\ell$ for $\nu$ is contained in its eigenspace, i.e. $T_\ell$ is semisimple. Secondly, there is a family $v:\mathbb N\to$ cusp forms of this level with $v_d(\tau)=g(d\tau)$ for all $d\mid N/M_g$ (the action being by [`ModularForm.heckeDiagMatrix d`](def/ModularForm_HeckeOperator.html#L21)), such that $(v_d)_{d\mid N/M_g}$ is $\mathbb C$-linearly independent, its span equals $\bigcap_{\ell\ \mathrm{prime},\ \ell\notin S}\ker(T_\ell-a_\ell(g))$, and for every prime $q\mid N$ and every $d\mid N/M_g$ one has $U_qv_d=v_{d/q}$ if $q\mid d$, $U_qv_d=a_q(g)v_d$ if $q\nmid d$ and $q\mid M_g$, and $U_qv_d=a_q(g)v_d-q\,v_{dq}$ if $q\nmid d$ and $q\nmid M_g$.
--
--   This is the Atkin–Lehner–Li description of the old classes attached to a newform $g$ of level $M_g\mid N$ inside weight-two cusp forms on $\Gamma_0(N)$: the degeneracy images $g(d\tau)$ form a basis of the common eigenspace for the Hecke operators away from $S$, with the explicit $U_q$-strings, together with semisimplicity of the good $T_\ell$. It feeds the Eichler–Shimura dimension computation [`CohCarrier.finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity`](thm.html#CohCarrier.finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity), where the multiplicity of an eigensystem in parabolic cohomology is evaluated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform) :

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (ν : ℂ),
      Module.End.maxGenEigenspace
          (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ hℓN) ν ≤
        Module.End.eigenspace (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ hℓN) ν) ∧

    ∃ v : ℕ → CuspForm (CohCarrier.GammaH N ⊤) 2,
      (∀ d : ℕ, d ∣ N / Mg → ∀ τ : UpperHalfPlane, v d τ = g (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun d : ↥(Nat.divisors (N / Mg)) => v (d : ℕ)) ∧
      Submodule.span ℂ (Set.range fun d : ↥(Nat.divisors (N / Mg)) => v (d : ℕ)) =
        ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S), Module.End.eigenspace
          (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ (fun h => hℓS (hNS ℓ hℓ h)))
          (ModularFormClass.qCoeff g ℓ) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (d : ℕ), d ∣ N / Mg →
        (q ∣ d → CuspForm.heckeULinH 2 q (v d) = v (d / q)) ∧
        (¬ q ∣ d → q ∣ Mg → CuspForm.heckeULinH 2 q (v d) = ModularFormClass.qCoeff g q • v d) ∧
        (¬ q ∣ d → ¬ q ∣ Mg → CuspForm.heckeULinH 2 q (v d) =
          ModularFormClass.qCoeff g q • v d - (q : ℂ) • v (d * q))) := by sorry
