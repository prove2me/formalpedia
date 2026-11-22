-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_corollary_3_11_exact_restriction
-- name    : CatalyticTreeEval.Main.corollary_3_11_exact_restriction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:19:33.209206+00:00
-- url     : https://prove2.me/theorems/adbfb9a4-d403-43c4-a2f8-9a64c741c128
-- title:
--   Appendix C — exact-size restriction of the parameterized construction
-- statement:
--   Assume the explicit uniform construction of Theorem 3.10, with one machine and one positive absolute constant. Appendix C chooses $\theta=\max(10,\lceil(\log\eta)/t^2\rceil)$, $w=\lceil\ell/\theta\rceil$, and $H=w2^\theta$, where $\eta=\ell^{t-1}/m$.
--
--   In the fixed-prime regime, for every $t\ge2$ and every fixed list of distinct odd primes, there is a native finite printer and a positive constant such that, for every $\ell\ge1$, restricting the $\binom Hw$-member canonical matching family to its first $2^\ell$ indices gives a family of exactly that size and dimension $\sum_{j=0}^{\lfloor(mw)^{1/t}\rfloor}\binom Hj$. Its access workspace is the Theorem 3.10 expression at these parameters, multiplied by the new positive constant.
--
--   In the variable-prime regime there is likewise one native printer and positive constant. Whenever $\binom Hw\ge2^\ell$, the same restriction gives an exact-size canonical family for the first $\lceil\sqrt{\log_2\ell}\rceil$ odd primes, with the corresponding explicit dimension and workspace expressions. The displayed size inequality deliberately exposes the restriction side condition; Appendix C discharges it from the parameter choice. In both regimes the final parameter string is just the encoding of $\ell$: the wrapper computes $w,H$ (and, in the variable-prime case, the primes) from $\ell$. Restriction does not change inner products, dimensions, or the printed coordinates.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Appendix C, proof of Corollary 3.11, printed pp.39-40 (PDF pp.41-42), especially the parameter choices and the paragraph restricting to the first 2^ell indices; Theorem 3.10, PDF p.18; Claim B.7, PDF p.40.

import Definitions.Def_CatalyticTreeEval_Corollary311Parameters

set_option autoImplicit false

/-- Appendix C, PDF pp.41-42: native parameterized families, exact restriction and headers. -/
theorem CatalyticTreeEval.Main.corollary_3_11_exact_restriction
    (M : Machine) (C : ℝ) (hC : 0 < C)
    (construction : LargeFamilyConstruction M C) :
    (∀ (t : ℕ) (p : Fin t → ℕ), 2 ≤ t → OddPrimeData p →
      ∃ (Mn : Machine) (Cn : ℝ), 0 < Cn ∧
        ∀ l : ℕ, 1 ≤ l →
        ∃ (U V : Fin (2 ^ l) → Vec (modulus p) (regimeDimension p l)),
          SMatching (canonical p (modulus p)) U V ∧
          VectorAccess Mn (natCode l) U V (Cn * regimeSpace p l)) ∧
    (∃ (M : Machine) (Cn : ℝ), 0 < Cn ∧
      ∀ l : ℕ, 1 + l ≤ (regimeHeight (firstOddPrimes (variablePrimeCount l)) l).choose
        (regimeWidth (firstOddPrimes (variablePrimeCount l)) l) →
      ∃ (U V : Fin (2 ^ l) →
        Vec (modulus (firstOddPrimes (variablePrimeCount l)))
          (regimeDimension (firstOddPrimes (variablePrimeCount l)) l)),
        SMatching (canonical (firstOddPrimes (variablePrimeCount l))
          (modulus (firstOddPrimes (variablePrimeCount l)))) U V ∧
        VectorAccess M (natCode l) U V
          (Cn * regimeSpace (firstOddPrimes (variablePrimeCount l)) l)) := by sorry
