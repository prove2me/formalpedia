-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_additiveFactor_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_additiveFactor_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T12:58:23.211723+00:00
-- url     : https://prove2.me/theorems/02b132d6-dd30-44d5-a78d-894d733eff08
-- title:
--   Proof of Proposition 7.2 of OpenAI's Primitive roots paper — the additive factor of the probe has squared row mass O(1/Y)
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every system of allowed generators $g$ (`AllowedGen ι 𝔪`), and all smooth real functions $W_1, V$ with compact support in $(0, \infty)$ (`IsProbeWeight`). There is $C$ such that for all real $X, Y$ with $1 \le Y \le X$ the sum over the row classes $r$ (`RowClass 𝔪`) of $|A_r|^2$, where $A_r = $ `additiveFactor g W₁ V X Y r`, converges (`HasSum`) to a value at most $C/Y$.
--
--   The bundle `Def_ArtinHeckeTheta` defines $A_r$ as $\sum_{\mathfrak s}Y^{-1}W_1(q_{\mathfrak s}/Y)(q_{\mathfrak s}X)^{-1/2}q_{\mathfrak s}^{-1/2}g_{\mathfrak s}(-m)V(q_m/(q_{\mathfrak s}X))$ for the row $m$ of class $r$: the additive factor of the probe (7.3) after the integral over $F_S^1/U_S^6$ is unfolded against the classes $mU_S^6$, with $V$ the norm-sheet profile of $W_0$. The paper bounds this mass at $(X, Y) = (Z^a, Z^b)$ with $b < a$; its argument (Lemma 7.1 with $N = XY$ and $V \ll Y$) gives the bound $(XY)^{-1}(XY + Y^2)/Y \ll Y^{-1}$ whenever $Y \le X$. The constant $C$ may depend on $\mathfrak m$, $g$, $W_1$ and $V$, as the paper's depends on $F$, $S$ and the weights.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 44, proof of Proposition 7.2: “Take $N = XY$ and $V \ll Y$ in Theorem 7.1. The bounded set of representatives $t_0$ only enlarges the fixed compact row box. By the triangle inequality for the Fourier series, the squared $\ell^2$ norm in $m$ of the whole additive factor in Equation (7.3), including $(q_{\mathfrak s}X)^{-1/2}$, is $\ll (XY)^{-1}\frac{XY + Y^2}{Y} \ll Y^{-1}$. The last inequality uses $b < a$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 44, proof of Proposition 7.2 (the squared row mass of the additive factor of (7.3) is O(Y^{-1}))

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_tsum_norm_sq_additiveFactor_le (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (W₁ V : ℝ → ℝ), IsProbeWeight W₁ → IsProbeWeight V →
        ∃ C : ℝ, ∀ X Y : ℝ, 1 ≤ Y → Y ≤ X →
          ∃ σ : ℝ, HasSum (fun r : RowClass 𝔪 => ‖additiveFactor g W₁ V X Y r‖ ^ 2) σ ∧
            σ ≤ C / Y := by
  sorry

end ArtinPrimitiveRoots
