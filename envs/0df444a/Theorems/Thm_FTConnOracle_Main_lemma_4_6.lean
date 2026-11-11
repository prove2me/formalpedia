-- Prove2me | Theorems.Thm_FTConnOracle_Main_lemma_4_6
-- name    : FTConnOracle.Main.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:36:11.880936+00:00
-- url     : https://prove2.me/theorems/b264977b-99cc-4bf5-a729-45b7b79239cf
-- title:
--   Lemma 4.6 — a family of 2^{n−1} masks with (n−1)-bit identifiers that is O(n^{3/2}√log n)-good, good masks found in polynomial time
-- statement:
--   There are a universal constant $C>0$ and, for every even $n\ge2$, a family of masks $\mathcal M_n=\{M_x : x\in\{0,1\}^{n-1}\}$ on $[n]$ such that, with $D_n=C\,n^{3/2}\sqrt{\log n}$:
--
--   1. $|\mathcal M_n|=2^{n-1}$, each mask has a unique $(n-1)$-bit identifier $x$, and one polynomial-time machine computes $M_x$ (its adjacency bits) from $(1^n,x)$, for every even $n\ge2$;
--   2. $\mathcal M_n$ is $D_n$-good: every graph $H$ on $[n]$ has a mask $M_x$ that is $D_n$-good for $H$;
--   3. one polynomial-time machine, given $G$ (as $(1^n,\text{adjacency bits of }G)$), outputs the identifier $x$ of a mask $M_x$ that is $D_n$-good for $G$, for every even $n\ge2$.
--
--   $$\exists C>0\ \exists(\mathcal M_n)_n:\ |\mathcal M_n|=2^{n-1},\quad \forall H\ \exists M\in\mathcal M_n:\ M\text{ is }C n^{3/2}\sqrt{\log n}\text{-good for }H,\ \text{identifiers decoded and good masks found in polynomial time}.$$
--
--   The family turns each level of the hierarchy of §4.3 into an $(n-1)$-bit identifier, which is what makes the $\tilde O(n^{7/4})$ bound possible.
--
--   **Formalization Note.** Logarithms are natural. The family is `Set.range (mask n)` for a function `mask n : ({0,1}^{n-1}) → graphs on [n]`; injectivity of `mask n` is the uniqueness of identifiers. Polynomial time is `LowErrExt.IsPolyTime` with the codes of the `Codes` definition.
--
--   Differences from the source:
--   - encoding: O(n^{3/2}√(log n)) in items 2 and 3 → C·n^{3/2}·√(log n) with one universal C > 0 quantified before n, the same C in items 2 and 3; reason: standard meaning of O(·); D-goodness is monotone in D, so one constant for both items is equivalent to two
--   - encoding: a family M_n of masks with unique (n − 1)-bit identifiers, |M_n| = 2^{n−1} → mask n : (Fin (n − 1) → Bool) → SimpleGraph (Fin n) injective, M_n = Set.range (mask n) with ncard 2^{n−1}; reason: same object: the identifier map is a bijection onto the family
--   - reading: computed in polynomial time (item 1); can be found deterministically in polynomial time (item 3) → one polynomial-time machine (LowErrExt.IsPolyTime) for all even n: (1^n, x) ↦ adjacency bits of mask n x; (1^n, adjacency bits of G) ↦ the identifier bits of a good mask; reason: 'polynomial time' read as one uniform algorithm in the input length (Θ(n) resp. Θ(n²)); finding a mask is outputting its identifier, from which item 1 computes it
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 23 (PDF 25), Lemma 4.6; construction in Appendix B, pp. 50–51 (PDF 52–53)

import Mathlib
import Definitions.Def_FTConnOracle_Main_Mask
import Definitions.Def_FTConnOracle_Main_Codes
import Definitions.Def_LowErrExt_IsPolyTime

namespace FTConnOracle.Main

/-- Lemma 4.6 (p. 23): there are a universal `C > 0` and, for every even `n ≥ 2`, a family of masks
`𝓜_n = {mask n x : x ∈ {0,1}^{n−1}}` such that
1. `|𝓜_n| = 2^{n−1}`, each mask has a unique `(n−1)`-bit identifier, and one polynomial-time
   machine computes the mask (its adjacency bits) from `(n, x)`;
2. `𝓜_n` is `C n^{3/2} √(log n)`-good;
3. one polynomial-time machine, given `G`, outputs the identifier of a mask that is
   `C n^{3/2} √(log n)`-good for `G`. -/
theorem lemma_4_6 :
    ∃ C : ℝ, 0 < C ∧
      ∃ mask : (n : ℕ) → (Fin (n - 1) → Bool) → SimpleGraph (Fin n),
        (∀ n : ℕ, 2 ≤ n → Even n →
          (Set.range (mask n)).ncard = 2 ^ (n - 1) ∧ Function.Injective (mask n)) ∧
        (∃ A : List (List Bool) → List Bool, LowErrExt.IsPolyTime A ∧
          ∀ n : ℕ, 2 ≤ n → Even n → ∀ x : Fin (n - 1) → Bool,
            A (maskInput n x) = adjBits (mask n x)) ∧
        (∀ n : ℕ, 2 ≤ n → Even n →
          IsDGoodFamily (C * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (Real.log (n : ℝ)))
            (Set.range (mask n))) ∧
        (∃ A : List (List Bool) → List Bool, LowErrExt.IsPolyTime A ∧
          ∀ n : ℕ, 2 ≤ n → Even n → ∀ G : SimpleGraph (Fin n),
            ∃ x : Fin (n - 1) → Bool, A (graphInput G) = idBits x ∧
              IsDGood (C * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (Real.log (n : ℝ)))
                (mask n x) G) := by sorry

end FTConnOracle.Main
