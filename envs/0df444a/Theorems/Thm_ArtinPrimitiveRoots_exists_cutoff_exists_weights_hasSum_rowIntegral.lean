-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_weights_hasSum_rowIntegral
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_weights_hasSum_rowIntegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T12:59:29.147401+00:00
-- url     : https://prove2.me/theorems/130cacb9-90de-48d2-bf98-57431261b442
-- title:
--   (7.1) and (7.10) of OpenAI's Primitive roots paper — for suitable weights the probe is the sum of its Poisson rows
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, every system of allowed generators $g$ (`AllowedGen ι 𝔪`), and every smooth real $W_1$ with compact support in $(0, \infty)$ (`IsProbeWeight W₁`). There are a smooth real $V$ with compact support in $(0, \infty)$ and a function $M : \mathbb C \to \mathbb C$, holomorphic on $\operatorname{Re} z > 0$ with rapid vertical decay on its strips (`IsMellinWeight M`) and $M(1/6) \ne 0$, such that for all real $X, Y, Z > 0$ the rows `χ.rowIntegral g W₁ M r X Y Z`, over the frequency classes $r$ (`FreqClass 𝔪`), sum (`HasSum`) to the probe `χ.probe g W₁ V X Y Z`.
--
--   In the paper, $V$ is the norm-sheet profile $T \mapsto \int_{F_S^1}W_0(t\ell_T)\,dt$ of the weight $W_0$ of (7.1), and $M$ is the Mellin transform in (7.1), that is, of the profile $V_0$ of $\widehat W_0$ (p. 45). With them the probe is the paper's $I(X, Y, Z)$ of (7.3), and each row is the term of (7.10) for one $u \in \mathcal U$; the bundle note of `Def_ArtinHeckeTheta` gives the unfolding. The statement packages the choice of weights in (7.1), whose existence the paper derives from Tate's local functional equation, with the Poisson identity (7.10) that it derives from Lemma 3.1, (7.8) and Mellin inversion.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 42: “Choose a tensor Bruhat–Schwartz function $W_0$ on $F_S$, compactly supported in $F_S^\times$, such that $\widehat W_0(0) = 0$, $M(1/6) \ne 0$, $M(z) = \int_{F_S^\times}\widehat W_0(y)|y|_S^z\,d^\times y$. (7.1)”; p. 42: “Thus $M$ is holomorphic for $\operatorname{Re} z > 0$, and integration by parts in that norm gives, for every compact interval $J \subset (0, \infty)$ and every $A > 0$, $|M(\sigma + i\tau)| \ll_{J,A} (1 + |\tau|)^{-A}$ $(\sigma \in J)$. (7.2)”; and p. 46: “We obtain $I(X, Y, Z) = \frac{1}{(2\pi i)^3}\int_{(4)}\int_{(4)}\int_{(2)}X^{1/2-z}Z^{\xi+z-1}Y^{w-1}e^{(\xi+z-1)^2}M(z)\widehat W_1(w)\times\sum_{u \in \mathcal U}q_u^{-z}\mathcal F_u(\xi, w, z)\,dz\,dw\,d\xi$ (7.10) […] All interchanges used for Equation (7.10) are in absolute convergence.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 42, 45–46, (7.1) and (7.10) (the weights and the Poisson expression of the probe)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_weights_hasSum_rowIntegral (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ : ℝ → ℝ), IsProbeWeight W₁ →
        ∃ (V : ℝ → ℝ) (M : ℂ → ℂ), IsProbeWeight V ∧ IsMellinWeight M ∧ M (1 / 6) ≠ 0 ∧
          ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
            HasSum (fun r : FreqClass 𝔪 => χ.rowIntegral g W₁ M r X Y Z)
              (χ.probe g W₁ V X Y Z) := by
  sorry

end ArtinPrimitiveRoots
