-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_norm_rowIntegral_principalFreq_sub_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_norm_rowIntegral_principalFreq_sub_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T13:00:16.682344+00:00
-- url     : https://prove2.me/theorems/454a8a23-d3e2-42a5-a2dd-954820cb3124
-- title:
--   (8.12)–(8.13) of OpenAI's Primitive roots paper — the principal row of the probe is c₀ f_η(Z) + O(Z^{7/15 − .0005})
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, every system of allowed generators $g$ (`AllowedGen ι 𝔪`), every smooth real $W_1$ with compact support in $(0, \infty)$ (`IsProbeWeight W₁`) and every $M$ holomorphic on $\operatorname{Re} z > 0$ with rapid vertical decay on its strips (`IsMellinWeight M`). There are $C$ and $Z_0$ such that for every real $Z \ge Z_0$
--   $$\bigl|J_1(Z^{9/10}, Z^{133/1000}, Z) - c_0 f_\eta(Z)\bigr| \le C Z^{7/15 - 1/2000},$$
--   where $J_1 = $ `χ.rowIntegral g W₁ M (principalFreq 𝔪)` is the row $u = 1$ of (7.10), $c_0 = (R_S^2/6)M(1/6)\widehat W_1(1)$ is `principalConstant 𝔪 W₁ M` with $R_S$ the residue at $s = 1$ of the Dedekind zeta function with the factors at the primes dividing $\mathfrak m$ removed, and $f_\eta(Z) = $ `χ.principalMellin ι Z` is the integral (8.13).
--
--   The paper writes the principal row as $I_1(Z) = c_0f_\eta(Z) + R_w(Z) + R_z(Z)$ with both remainders $O(Z^{C_*(1) - .0005})$, $C_*(1) = 7/15$; the statement is that $I_1 - c_0f_\eta = R_w + R_z$ is $O(Z^{7/15 - .0005})$. The scales are $X = Z^a$ and $Y = Z^b$ with $a = 9/10$ and $b = 133/1000$, (4.4). The constants may depend on $\mathfrak m$, $\chi$, $g$, $W_1$ and $M$, as the paper's depend on $F$, $S$, $\eta$, $W_0$ and $W_1$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 56: “Let $I_1(Z)$ denote the contribution of $u = 1$ to the initially absolutely convergent formula Equation (7.10), on the scales $(X, Y) = (Z^a, Z^b)$. […] The other term is the double residue. With its evaluation $c_0f_\eta(Z)$ below, the principal component is exactly $I_1(Z) = c_0f_\eta(Z) + R_w(Z) + R_z(Z)$. […] The height bounds just given and Theorem 7.3 therefore give $R_w(Z) = O_{F,S,\eta,W_0,W_1}(Z^{C_*(1)-.0005})$, $R_z(Z) = O_{F,S,\eta,W_0,W_1}(Z^{C_*(1)-.0005})$. (8.12) To evaluate the double residue, write $R_S = \operatorname{Res}_{s=1}\zeta_F^S(s) > 0$. It has the form $c_0f_\eta(Z)$, where $c_0 = \frac{R_S^2}{6}M(1/6)\widehat W_1(1) \ne 0$, $f_\eta(Z) = \frac{1}{2\pi i}\int_{(2)}Z^{C_*(\xi)}e^{(\xi-5/6)^2}\frac{\mathcal H_\eta(\xi)}{L^S(\xi, \eta)}\,d\xi$. (8.13)” Here “Theorem 7.3” is the paper's Proposition 7.3.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 56, (8.12)–(8.13) (the principal row)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_norm_rowIntegral_principalFreq_sub_le (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ : ℝ → ℝ) (M : ℂ → ℂ),
        IsProbeWeight W₁ → IsMellinWeight M →
          ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
            ‖χ.rowIntegral g W₁ M (principalFreq 𝔪) (Z ^ ((9 : ℝ) / 10))
                (Z ^ ((133 : ℝ) / 1000)) Z - principalConstant 𝔪 W₁ M * χ.principalMellin ι Z‖ ≤
              C * Z ^ ((7 : ℝ) / 15 - 1 / 2000) := by
  sorry

end ArtinPrimitiveRoots
