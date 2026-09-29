-- Prove2me | Theorems.Thm_AutomorphicForm_sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
-- name    : AutomorphicForm.sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/fdb867bf-a395-5cce-8a65-6c2cd1a72da0
-- title:
--   Local Hecke slot combination at a split shell class
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $ws$ assign to each height-one prime $v$ of $\mathcal O_K$ an extension of $v$ to $\mathcal O_L$ (a prime $w$ of $\mathcal O_L$ with $w$ under $K$ equal to $v$), fix $v$ and naturals $k,j$, and write $f = \mathrm{slotDeg}$ for the inertia degree of $(ws\,v)$ over $v$, assumed positive. Assume $\mathrm{absNorm}$ of the ideal of $(ws\,v)$ equals $Nw$ and $Nw = (\mathrm{absNorm}\,v)^f$, and let $\zeta,s,x \in \mathbb C$ satisfy $\zeta \neq 0$, $s^2 = \zeta$, $x^f = \zeta$. Let $\varpi$ be an irreducible element of the valuation ring $\mathcal O_v$ with nonzero image in $K_v$, let $rT : \mathrm{Fin}\,n \to \mathrm{GL}_2(K_v)$ be a Hecke coset system for the subgroup $U$ of matrices coming from $\mathcal O_v$ and the element $\mathrm{diag}(\varpi,1)$ (each $rT\,i$ lies in the double coset $U\,\mathrm{diag}(\varpi,1)\,U$, every element of that double coset lies in some left coset $rT\,i\cdot U$, and $i \mapsto rT\,i\,U$ is injective), and let $z \in \mathrm{GL}_2(K_v)$ have matrix $\varpi \cdot 1$. Let $u \in K_v$ with $u \neq 0$, $u \neq 1$ and $\lVert u\rVert = \lVert \varpi\rVert^{d}$ for an integer $d$, and let $t\,e$ have matrix $\mathrm{diag}(\varpi^e u, \varpi^e)$ for $e \in \mathbb Z$. For each $e$ let $\tau\,e$ be a Haar measure on the centraliser of $t\,e$ (with its Borel structure) giving mass $1$ to the intersection of the centraliser with the set of $g$ such that both $g$ and $g^{-1}$ have entries in $\mathcal O_v$. Finally let $I : (\mathrm{Fin}\,2 \to_{f_0} \mathbb N) \to \mathbb Z \to \mathbb C$ be such that for every exponent $r$ in the support of $\mathrm{slotWord} = \mathrm{satakePow}\,f\,(X_0)\,(X_1)^k \cdot (X_1^{f})^{j}$ and every $e$, the number $I\,r\,e$ is an orbital integral of $t\,e$ against $\tau\,e$ for the function $y \mapsto \sum_{\iota : \mathrm{Fin}(r\,0) \to \mathrm{Fin}\,n}$ of the indicator of the integral set at $\bigl((\prod_i rT(\iota\,i))\,z^{r\,1}\bigr)^{-1} y$, i.e. there is a nonnegative measurable compactly supported weight $w$ on $\mathrm{GL}_2(K_v)$ whose integral over the centraliser of the translate $t \mapsto w(t x)$ is $1$ whenever the function does not vanish at $x^{-1}(t\,e)x$, and $I\,r\,e$ is the integral of that function at $x^{-1}(t\,e)x$ times $w(x)$ against the Haar measure on $\mathrm{GL}_2(K_v)$ normalised by the integral set. Then for each such $r$ the family $e \mapsto \lVert x^e\, I\,r\,e\rVert$ is summable, and $\sum_r \mathrm{slotCoeff}(r)\sum_{e \in \mathbb Z} x^e\,I\,r\,e$, where $\mathrm{slotCoeff}(r)$ is the coefficient of $\mathrm{slotWord}$ at $r$ times $(\mathrm{absNorm}\,v)^{r\,1}$ divided by $Nw^{j}$, equals $\lVert u - 1\rVert^{-1}$ times $(\sqrt{Nw}\,s)^k \zeta^j$ times the coefficient of $(T + T^{-1})^k$ in the Laurent polynomial ring over $\mathbb C$ at degree $d/f$ times $(\sqrt{Nw}\,s)^{-(d/f)}$ if $f \mid d$, and $0$ otherwise.
--
--   This is the local computation at a Hecke place: the Satake-type combination of orbital integrals of the Hecke words $(\mathrm{diag}(\varpi,1))$-double-coset products times central powers, evaluated on the shells $\mathrm{diag}(\varpi^e u, \varpi^e)$ of a split regular class, is expressed by a single Laurent coefficient of $(T+T^{-1})^k$ with the expected volume factor $\lVert u-1\rVert^{-1}$. It is the per-place input to the two packaging statements that assemble the slot-family Hecke combination over all classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow.lean

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.sum_slotCoeff_mul_tsum_pow_mul_eq_inv_norm_sub_one_mul_ite_of_isOrbitalIntegral_heckeWord_diagonal_zpow
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (k j : ℕ)
    (hf : 0 < AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (Nw : ℕ) (hNw : Ideal.absNorm (ws v).1.asIdeal = Nw)
    (hNwf : Nw = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (ζ s x : ℂ) (hζ : ζ ≠ 0) (hs : s ^ 2 = ζ)
    (hx : x ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ)

    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))

    (u : v.adicCompletion K) (hu0 : u ≠ 0) (hu1 : u ≠ 1) (d : ℤ)
    (hud : ‖u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ d)

    (t : ℤ → GL (Fin 2) (v.adicCompletion K))
    (ht : ∀ e : ℤ, (t e : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖ : v.adicCompletion K) ^ e * u, (ϖ : v.adicCompletion K) ^ e])
    (τ : ∀ e : ℤ, @Measure (AutomorphicForm.localCentralizer K v (t e)) (AutomorphicForm.localCentralizerBorel K v (t e)))
    (hτ : ∀ e : ℤ, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (t e)) (τ e))
    (hτ1 : ∀ e : ℤ, τ e (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (I : (Fin 2 →₀ ℕ) → ℤ → ℂ)
    (hI : ∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support, ∀ e : ℤ,
      AutomorphicForm.IsOrbitalIntegral K v (t e) (τ e)
        (fun y : GL (Fin 2) (v.adicCompletion K) =>
          ∑ ι : Fin (r 0) → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun i => rT (ι i)).prod * z ^ (r 1))⁻¹ * y)) (I r e)) :
    (∀ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
        Summable fun e : ℤ => ‖x ^ e * I r e‖) ∧
    ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
        AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r * ∑' e : ℤ, x ^ e * I r e =
      ((‖u - 1‖ : ℝ) : ℂ)⁻¹ *
        (if (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ) ∣ d then
          ((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ k * ζ ^ j *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff
                (d / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ)) *
            (((Real.sqrt (Nw : ℝ) : ℂ) * s) ^ (-(d / (AutomorphicForm.SatakeCombination.slotDeg K L ws v : ℤ))))
        else 0) := by sorry
