-- Prove2me | Theorems.Thm_AutomorphicForm_integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue
-- name    : AutomorphicForm.integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/2421c67a-eae2-5991-bc2a-278c5d18696d
-- title:
--   Twisted weighted word orbital integral at an inert place
-- statement:
--   Let $L/K$ be an extension of number fields, $v$ a nonzero prime of $\mathcal O_K$ and $w$ a prime of $\mathcal O_L$ lying over $v$, assumed unramified (relative ramification index $1$) and of prime local degree $\ell = [L_w : K_v]$; let $\theta$ be a $K_v$-algebra automorphism of $L_w$ of order $\ell$ for which some $y$ with $\|y\|\le 1$ satisfies $\|\theta y - y\| = 1$. Let $\varpi$ be an irreducible element of the valuation ring $\mathcal O_w$, nonzero in $L_w$, let $r_0,\dots,r_{n-1} \in \mathrm{GL}_2(L_w)$ be a system of representatives for the left cosets of the integral subgroup $\mathrm{GL}_2(\mathcal O_w)$ (the image of $\mathrm{GL}_2$ of $\mathcal O_w$) contained in the double coset of $\mathrm{diag}(\varpi,1)$ — each $r_i$ lies in that double coset, every element of it is left-congruent to some $r_i$, and the cosets $r_i U$ are pairwise distinct — let $z$ be the scalar matrix $\varpi\cdot 1$, and let $k,j$ be natural numbers. Let $a \ne b$ be units of $K_v$ and $\alpha,\beta$ units of $L_w$ with $\prod_{i<\ell}\theta^i(\alpha) = a$ and $\prod_{i<\ell}\theta^i(\beta) = b$, and assume that the $\sigma$-twisted centralizer $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta = \mathrm{diag}(\alpha,\beta)$, where $\sigma$ is the automorphism of $\mathrm{GL}_2(L_w)$ induced by $\theta$, is the image of the centralizer of $\mathrm{diag}(a,b)$ in $\mathrm{GL}_2(K_v)$ under the map induced by $K_v \hookrightarrow L_w$. Write $\|\alpha\| = N(w)^{-r_a}$, $\|\beta\| = N(w)^{-r_b}$ with $r_a, r_b \in \mathbb Z$, and let $d \in \mathbb N$ be such that $r_a = r_b$ implies $\|1 - ba^{-1}\| = N(v)^{-d}$, where $N$ denotes absolute norm of the corresponding prime ideal. Let $\tau'$ be a Haar measure on the twisted centralizer, for its Borel structure, of total mass $1$ on the set of its elements $t$ whose matrix and inverse matrix have entries in $\mathcal O_w$, and let $s : \mathrm{GL}_2(L_w) \to \mathbb R$ be nonnegative, Borel measurable and compactly supported, with $\int s(tx)\,d\tau'(t) = 1$ for every $x$ at which the word kernel $\Phi(x) = \sum_{\iota : \{0,\dots,k-1\} \to \{0,\dots,n-1\}} \mathbf 1_{\mathrm{GL}_2(\mathcal O_w)}\bigl((r_{\iota(0)}\cdots r_{\iota(k-1)}z^j)^{-1}\,x^{-1}\delta\,\sigma(x)\bigr)$ does not vanish. Let $W_Q : \mathbb N \to \mathbb N \to \mathbb N$ satisfy the walk recursion $W_Q(0,0)=1$, $W_Q(0,s+1)=0$, $W_Q(m+1,0) = (N(v)^{\ell}+1)W_Q(m,1)$ and $W_Q(m+1,s+1) = W_Q(m,s) + N(v)^{\ell}W_Q(m,s+2)$; let $\varphi(a',s) = W_Q(k,s)$ if $2a'+s = k+2j$ and $0$ otherwise; and let $P(0)=1$, $P(i) = \bigl(N(v)^{(\ell-1)(i-1)}\sum_{t<\ell}N(v)^{t}\bigr)^{-1}$ for $1 \le i \le d$, and $P(i) = 0$ for $i > d$. Then, with respect to the Haar measure on $\mathrm{GL}_2(L_w)$ normalised by the integral compacts, $\int \Phi(x)\,w(x)\,s(x)\,dx$, where $w(x) = 2\log\bigl(\max(\|x_{00}\|,\|x_{01}\|)\cdot\mathrm{rowMaxNorm}(x)/\|\det x\|\bigr)$, equals $2\log N(v)$ times the value which is $0$ unless $r_a + r_b = k + 2j$, and in that case is $\sum_{m=1}^{r_a + d} \ell\,m\,(N(v)^{\ell})^{m}(1 - N(v)^{-\ell})\bigl(\varphi(r_a,0)P(m) + \sum_{i=0}^{\min(d,m-1)}(P(i)-P(i+1))\varphi(r_a-(m-i),2(m-i))\bigr)$ if $r_a = r_b$, and $\sum_{m=1}^{\min(r_a,r_b)} \ell\,m\,(N(v)^{\ell})^{m}(1-N(v)^{-\ell})\,\varphi(\min(r_a,r_b)-m,\,|r_a-r_b|+2m)$ otherwise (upper limits truncated to their nonnegative parts, and differences of natural numbers formed in $\mathbb N$).
--
--   This is the evaluation, at an unramified place of prime local degree, of the weighted twisted orbital integral of the Hecke word kernel on $\mathrm{GL}_2(L_w)$ — the base-change ("$L$") side of a local twisted trace-formula comparison, expressed through walk counts for the $\mathrm{diag}(\varpi,1)$ double coset and a shell law $P$. It is used by [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank), where it is matched against the corresponding integral over $\mathrm{GL}_2(K_v)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)

    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (k j : ℕ)

    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (w.1.adicCompletion L)ˣ)
    (hNα : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) (α : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a)
    (hNβ : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) (β : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) b)
    (hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))))
    (ra rb : ℤ) (hα : ‖(α : w.1.adicCompletion L)‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-ra))
    (hβ : ‖(β : w.1.adicCompletion L)‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-rb))
    (d : ℕ) (hd : ra = rb →
      ‖1 - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))

    (τ' : @Measure (AutomorphicForm.sigmaCentralizer
        (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1)
    (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable[AutomorphicForm.localGLBorel L w.1] s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      (∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rL (ι m)).prod * z ^ j)⁻¹ *
            (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x))) ≠ 0 →
        ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom)
            (diagUnits2 α β), s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ' = 1)

    (WQ : ℕ → ℕ → ℕ) (hWQ00 : WQ 0 0 = 1) (hWQ0s : ∀ s : ℕ, WQ 0 (s + 1) = 0)
    (hWQroot : ∀ n : ℕ, WQ (n + 1) 0 = (Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) + 1) * WQ n 1)
    (hWQstep : ∀ n s : ℕ, WQ (n + 1) (s + 1) = WQ n s + Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) * WQ n (s + 2))
    (φ : ℤ → ℕ → ℂ)
    (hφ : ∀ (a : ℤ) (s : ℕ), φ a s = if 2 * a + s = (k : ℤ) + 2 * j then (WQ k s : ℂ) else 0)
    (P : ℕ → ℂ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((Ideal.absNorm v.asIdeal : ℂ) ^ ((Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1) * (i - 1)) * ∑ t ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (Ideal.absNorm v.asIdeal : ℂ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0) :
    ∫ x : GL (Fin 2) (w.1.adicCompletion L),
        (∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rL (ι m)).prod * z ^ j)⁻¹ *
            (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x))) *
          ((AutomorphicForm.LocalWeight.weight x : ℝ) : ℂ) * (s x : ℂ)
      ∂(AutomorphicForm.localHaar L w.1) =
      ((2 * Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
      (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          ∑ m ∈ Finset.Icc 1 (ra.toNat + d),
            (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) : ℂ) * m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))) ^ m * (1 - ((Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)))⁻¹) *
              (φ ra 0 * P m +
                ∑ i ∈ Finset.range (min d (m - 1) + 1),
                  (P i - P (i + 1)) * φ (ra - ((m - i : ℕ) : ℤ)) (2 * (m - i)))
        else
          ∑ m ∈ Finset.Icc 1 (min ra rb).toNat,
            (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) : ℂ) * m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))) ^ m * (1 - ((Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)))⁻¹) *
              φ (min ra rb - m) ((ra - rb).natAbs + 2 * m))
      else 0) := by sorry
