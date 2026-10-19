-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_prod_gaussPhase_three_span_eq_one
-- name    : ArtinPrimitiveRoots.exists_cutoff_prod_gaussPhase_three_span_eq_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T09:23:01.009992+00:00
-- url     : https://prove2.me/theorems/e57b07ac-87d3-4be4-8ea1-8c880db332c3
-- title:
--   The quadratic Gauss sums γ₃ of OpenAI's Primitive roots paper give a character trivial on (α) for α ≡ 1 mod 𝔪^j — ∏_{𝔭 ∣ α} γ₃(𝔭)^{v_𝔭(α)} = 1
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`) there is $j \ge 0$ such that for every nonzero $\alpha \in \mathcal O_F$ with $\alpha - 1 \in \mathfrak m^j$,
--   $$\prod_{\mathfrak p} \gamma_3(\mathfrak p)^{v_{\mathfrak p}(\alpha)} = 1,$$
--   the product over the prime factors of $\alpha\mathcal O_F$ counted with multiplicity, where $\gamma_3$ = `gaussPhase g 3` is the normalized quadratic Gauss sum (3.8) with the allowed generator of $\mathfrak p$.
--
--   This is a cut for `exists_cutoff_exists_sChar_sEmb_gen_eq_thetaChar_mul_residueSymbol`, used with `exists_cutoff_exists_gaussLambda_span_eq_prod_toCircle`; that reduction is proved in Lean.
--
--   In the paper this is the part of Lemma 3.4 (pp. 13–15) about $G$ beyond $\chi_\bullet(4)$: $\gamma_3(\mathfrak p) = \mathfrak w_S(p^{-1})^{-1}$, from Weil's product formula for the normalized Weil index (3.13) (p. 14), is a character of the class of the allowed generator in $B$, extended to a finite-order Hecke character unramified outside $S$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 14: “Put $\mathfrak w_S = \prod_{v\in S}\mathfrak w_v$. Applying the first identity of Equation (3.13) to $p^{-1}$, all exterior places other than $\mathfrak p$ contribute 1, and hence $\gamma_3(\mathfrak p) = \mathfrak w_S(p^{-1})^{-1}$. On $B$ the multiplicative defect in the second identity is $\prod_{v\in S}(a,b)_{2,v} = H_S(a,b)^3 = 1$.”
--
--   **Formalization note.** `AllowedGen` does not record that the generator classes lie in $B$; the statement is made for every system of allowed generators. "Finite-order Hecke character unramified outside $S$" is stated through its values on principal ideals $(\alpha)$, $\alpha \equiv 1 \pmod{\mathfrak m^j}$.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 13–15, Lemma 3.4, the quadratic part of G: γ₃(𝔭) = 𝔴_S(p⁻¹)⁻¹ by the Weil index product formula (3.13), a character of the generator classes in B (trivial on principal ideals (α), α ≡ 1 mod 𝔪^j); a cut for exists_cutoff_exists_sChar_sEmb_gen_eq_thetaChar_mul_residueSymbol

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

theorem exists_cutoff_prod_gaussPhase_three_span_eq_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∃ j : ℕ, ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 ^ j →
      ((normalizedFactors (Ideal.span {α})).map fun P => gaussPhase g 3 P).prod = 1
  := by
  sorry

end ArtinPrimitiveRoots
