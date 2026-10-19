-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_sChar_sEmb_gen_eq_thetaChar_mul_residueSymbol
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_sChar_sEmb_gen_eq_thetaChar_mul_residueSymbol
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T08:41:25.474945+00:00
-- url     : https://prove2.me/theorems/557f2ece-d308-4282-a85b-fbe61bc86ee3
-- title:
--   The characters L_υ = L_S λ_ε of OpenAI's Primitive roots paper in the model — unitary, of angular type ±1, trivial on U_S, with L_υ(gen 𝔄) = ϑ(𝔄) χ_𝔄(ε)
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), every finite-order Hecke character $\chi$ of modulus $\mathfrak m$ and every system of allowed generators $g$ (`AllowedGen ι 𝔪`) there is $k_0$ such that for every level $k \ge k_0$ and every $\upsilon \in U_S/U_S^6$ (`SClass 𝔪`) there are $L_f :$ `SFin 𝔪 k` $\to \mathbb C$ and $m : W \to \mathbb Z$ ($W$ the infinite places) with
--   - $m(w) = \pm1$ for every $w$, $L_f(a + b) = L_f(a)L_f(b)$ and $|L_f(a)| = 1$;
--   - with $L(y) = L_f(y_3)\prod_w e^{i\,m(w)\,y_2(w)}$ on `SModel 𝔪 k` (the bundle `Def_ArtinHeckeSModel`; $y_2(w)$ is the argument at $w$ and $y_3$ the finite part): $L(\texttt{sEmb}\,\varepsilon) = 1$ for every $S$-unit $\varepsilon$, and $L(\texttt{sEmb}(g.\mathrm{gen}\,\mathfrak A)) = \vartheta(\mathfrak A)\,\chi_{\mathfrak A}(\upsilon.\mathrm{rep})$ for every exterior ideal $\mathfrak A$, with $\vartheta$ = `χ.thetaChar g` and $\chi_{\mathfrak A}$ = `residueSymbol ι 𝔪 𝔄`.
--
--   This is a cut for `exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker`, used with `exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_radial` and `exists_cutoff_finite_sFinCls_and_exists_addSubgroup_mem_iff_mem_range_pow_six`; that reduction is proved in Lean.
--
--   In the paper $L$ is $L_{\upsilon} = L_S\lambda_{\varepsilon}$ of (6.2) (p. 28): $L_S$ is the $S$-component of the idele-class character $\vartheta = \overline\Lambda\,\overline G\,\eta$ of Lemma 3.4, with (3.14) (p. 15), and $\lambda_\varepsilon = H_S(\varepsilon, \cdot)^{-1}$ has value $\chi_{\mathfrak A}(\varepsilon)$ at an allowed generator by (3.5) (p. 11).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 28: “With the character $L_S$ from Equation (3.14), put $L_{\upsilon_m} = L_S\lambda_{\varepsilon_m}$. Then $L_{\upsilon_m}(A) = \vartheta(\mathfrak A)\chi_{\mathfrak A}(\varepsilon_m)$ for every allowed generator $A$. (6.2) These characters form a fixed finite family. They are smooth, unitary, and trivial on $U_S$; their radial components at infinity are trivial, and their angular component at each complex place has power 1 or −1.”
--
--   **Formalization note.** $\varepsilon_m$ is the representative `υ.rep` of the unit class of the row. Smoothness becomes the factorization through `SFin 𝔪 k` for every large level $k$.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 11, 13–15, 28, Lemma 3.4, (3.14), (3.5) and (6.2) (the characters L_υ = L_S λ_ε, with L_υ(A) = ϑ(𝔄) χ_𝔄(ε)); a cut for exists_cutoff_exists_mellin_thetaAverage_eq_tsum_localWhittaker

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeSModel

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem exists_cutoff_exists_sChar_sEmb_gen_eq_thetaChar_mul_residueSymbol (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ υ : SClass 𝔪, ∃ (Lf : SFin 𝔪 k → ℂ) (m : InfinitePlace F → ℤ),
        (∀ w, m w = 1 ∨ m w = -1) ∧ (∀ a b, Lf (a + b) = Lf a * Lf b) ∧ (∀ a, ‖Lf a‖ = 1) ∧
        let L : SModel 𝔪 k → ℂ := fun y =>
          Lf y.2.2 * ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ)
        (∀ ε : SUnit 𝔪, L (sEmb 𝔪 k ((ε : Fˣ) : F)) = 1) ∧
        ∀ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 →
          L (sEmb 𝔪 k (g.gen 𝔄 : F)) = χ.thetaChar g 𝔄 * residueSymbol ι 𝔪 𝔄 υ.rep
  := by
  sorry

end ArtinPrimitiveRoots
