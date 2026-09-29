-- Prove2me | Theorems.Thm_AutomorphicForm_eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord
-- name    : AutomorphicForm.eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/fa13e752-7761-5182-9c81-8a1f5190f49b
-- title:
--   K-side value of a weighted word orbital integral
-- statement:
--   Let $K\subseteq L$ be number fields, $v$ a height-one prime of $\mathcal O_K$, and $ws$ a choice, for each height-one prime $u$ of $\mathcal O_K$, of a prime of $\mathcal O_L$ lying over it; assume the inertia degree of $(ws\,v)$ over $v$ equals $\ell=[L:K]$. Let $\varpi_K$ be an irreducible element of the valuation ring $\mathcal O_v$ of $K_v$, nonzero in $K_v$, let $r^K\colon \mathrm{Fin}\,n_K\to \mathrm{GL}_2(K_v)$ be a Hecke coset system for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) (the image of $\mathrm{GL}_2(\mathcal O_v)$) and the element $\mathrm{diag}(\varpi_K,1)$ — each $r^K_i$ lies in the double coset, every element of the double coset is left congruent to some $r^K_i$ modulo the subgroup, and $i\mapsto r^K_i U$ is injective — and let $z_K$ be the scalar matrix $\varpi_K\cdot 1$. Fix $k,j\in\mathbb N$ and distinct units $a\neq b$ of $K_v$, put $\gamma=\mathrm{diag}(a,b)$, and let $\tau$ be a Haar measure on the centraliser of $\gamma$ in $\mathrm{GL}_2(K_v)$ (Borel structure) giving mass $1$ to the set of centraliser elements $t$ with $t$ and $t^{-1}$ both integral. Let $J\in\mathbb C$ be a weighted orbital integral at $\gamma$ against $\tau$, in the sense of `IsWeightedOrbitalIntegral`, of the function $$x\mapsto \sum_{e\in\mathrm{supp}\,(\mathrm{slotWord}\,K\,L\,ws\,v\,k\,j)}\mathrm{slotCoeff}(e)\sum_{\iota\colon \mathrm{Fin}(e\,0)\to \mathrm{Fin}\,n_K}\mathbf 1_{\mathrm{GL}_2(\mathcal O_v)}\big((\textstyle\prod_m r^K_{\iota(m)}\cdot z_K^{e\,1})^{-1}x\big),$$ where $\mathrm{slotWord}=\mathrm{univWord}(\mathrm{slotDeg}\,K\,L\,ws\,v-1)\,k\,j$, the polynomial $\mathrm{univWord}(n)\,k\,j=\mathrm{satakePow}(n+1)(X_0,X_1)^k\,(X_1^{\,n+1})^j$, and $\mathrm{slotCoeff}(e)$ is the coefficient of $\mathrm{slotWord}$ at $e$ times $q^{e\,1}/N((ws\,v)_1)^{j}$, with $q=N(v)=$ `Ideal.absNorm v.asIdeal`. Assume $\|a\|=q^{-\ell r_a}$ and $\|b\|=q^{-\ell r_b}$ for integers $r_a,r_b$, and that $d\in\mathbb N$ satisfies $\|1-ba^{-1}\|=q^{-d}$ whenever $r_a=r_b$. Let $W_q\colon\mathbb N\to\mathbb N\to\mathbb N$ obey $W_q(0,0)=1$, $W_q(0,s+1)=0$, $W_q(n+1,0)=(q+1)W_q(n,1)$ and $W_q(n+1,s+1)=W_q(n,s)+q\,W_q(n,s+2)$, and let $f\colon\mathbb Z\to\mathbb N\to\mathbb C$ be given by $f(a',s)=\sum_{e}c_e\,q^{e\,1}q^{-\ell j}\,[\,2a'+s=e\,0+2\,e\,1\,]\,W_q(e\,0,s)$, the sum over the support of $\mathrm{univWord}(\ell-1)\,k\,j$ with $c_e$ its coefficients. Then $J=2\log q$ times the value which vanishes unless $r_a+r_b=k+2j$, and which in that case equals $f(\ell r_a,0)\sum_{s=1}^{d}s\,q^{s}(1-q^{-1})+\sum_{i=1}^{\ell\,r_a^{+}}(d+i)q^{d+i}(1-q^{-1})f(\ell r_a-i,2i)$ if $r_a=r_b$, and $\sum_{i=1}^{\ell\,(\min(r_a,r_b))^{+}} i\,q^{i}(1-q^{-1})\,f(\ell\min(r_a,r_b)-i,\ \ell\,|r_a-r_b|+2i)$ if $r_a\neq r_b$, where $(\cdot)^{+}$ denotes the truncation of an integer to a natural number.
--
--   This is the local evaluation, on the $K$-side, of the weighted orbital integral of the Hecke word attached to a profile $(k,j)$ at a regular split diagonal element whose eigenvalue norms are $\ell$-divisible, expressed through the walk counts $W_q$ on the tree of $\mathrm{GL}_2(K_v)$ and an Iwasawa shell sum. It feeds the comparison [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank) of twisted and untwisted weighted terms at an inert place in the base-change argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord.lean

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

theorem AutomorphicForm.eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hinert : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = Module.finrank K L)
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ e ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
          AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j e *
            ∑ ι : Fin (e 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x))
      J)

    (ra rb : ℤ) (ha : ‖(a : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((Module.finrank K L : ℤ) * ra)))
    (hb : ‖(b : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((Module.finrank K L : ℤ) * rb)))
    (d : ℕ) (hd : ra = rb →
      ‖1 - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))

    (Wq : ℕ → ℕ → ℕ) (hWq00 : Wq 0 0 = 1) (hWq0s : ∀ s : ℕ, Wq 0 (s + 1) = 0)
    (hWqroot : ∀ n : ℕ, Wq (n + 1) 0 = (Ideal.absNorm v.asIdeal + 1) * Wq n 1)
    (hWqstep : ∀ n s : ℕ, Wq (n + 1) (s + 1) = Wq n s + Ideal.absNorm v.asIdeal * Wq n (s + 2))
    (f : ℤ → ℕ → ℂ)
    (hf : ∀ (a : ℤ) (s : ℕ), f a s =
      ∑ e ∈ (AutomorphicForm.SatakeCombination.univWord (Module.finrank K L - 1) k j).support,
        (AutomorphicForm.SatakeCombination.univWord (Module.finrank K L - 1) k j).coeff e * (Ideal.absNorm v.asIdeal : ℂ) ^ (e 1) / (Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank K L * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0)) :
    J = ((2 * Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
      (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          f ((Module.finrank K L : ℤ) * ra) 0 * ∑ s ∈ Finset.Icc 1 d, (s : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ s * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) +
            ∑ i ∈ Finset.Icc 1 (Module.finrank K L * ra.toNat),
              ((d + i : ℕ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (d + i) * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * f ((Module.finrank K L : ℤ) * ra - i) (2 * i)
        else
          ∑ i ∈ Finset.Icc 1 (Module.finrank K L * (min ra rb).toNat),
            (i : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ i * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) *
              f ((Module.finrank K L : ℤ) * min ra rb - i) (Module.finrank K L * (ra - rb).natAbs + 2 * i))
      else 0) := by sorry
