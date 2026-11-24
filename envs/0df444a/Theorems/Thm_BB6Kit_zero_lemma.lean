-- Prove2me | Theorems.Thm_BB6Kit_zero_lemma
-- name    : BB6Kit.zero_lemma
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T22:13:14.390414+00:00
-- url     : https://prove2.me/theorems/72e59ad1-379e-49e1-8443-d81a95d0c335
-- title:
--   Mignotte–Voutier zero lemma (Prop. 3.11 and Sec. 4): a nonzero interpolation determinant exists
-- statement:
--   The zero estimate of the Mignotte–Voutier kit (Proposition 3.11, from Gouillon's zero lemma) together with its application in Section 4.
--
--   **Theorem.** Assume the standing hypotheses (real case, $\alpha_j>1$ integers, multiplicatively independent, $b_j>0$ coprime, $\Lambda\ne 0$), $K\ge 3$, $L\ge 5$, $N=K(K+1)L/2\le RST$, positive $R_j,S_j,T_j$ with (2.7), $\chi>0$, and conditions (2.9)–(2.13), with (2.10), (2.11) as cardinalities of $\{\alpha_1^r\alpha_2^s\alpha_3^t\}$. Assume also that neither (2.14) nor (2.15) holds. Then there are rows enumerating the index set and $N$ distinct columns in the box $[0,R)\times[0,S)\times[0,T)$ for which the interpolation determinant $\Delta$ of (2.6) is nonzero.
--
--   In the source: if the $N$ rows of the $N\times RST$ matrix were dependent, a nonzero polynomial would vanish on $\Sigma_1+\Sigma_2+\Sigma_3$, contradicting Proposition 3.11. Conditions (2.9)–(2.13) imply (3.17)–(3.19) via Lemmas 3.15, 3.17 and 3.21 unless (2.14) or (2.15) holds.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Proposition 3.11 (Gouillon, Lemma 3.12), Lemmas 3.15, 3.17, 3.21, and Section 4 (proof of Theorem 2.1).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem zero_lemma (K L R S T N b1 b2 b3 α1 α2 α3 R1 S1 T1 R2 S2 T2 R3 S3 T3 : ℕ) (χ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (hpos : 0 < R1 ∧ 0 < S1 ∧ 0 < T1 ∧ 0 < R2 ∧ 0 < S2 ∧ 0 < T2 ∧ 0 < R3 ∧ 0 < S3 ∧ 0 < T3)
    (h27 : R1 + R2 + R3 < R ∧ S1 + S2 + S3 < S ∧ T1 + T2 + T3 < T) (hχ : 0 < χ)
    (h29 : (K : ℝ) * (max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) < (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1)))
    (h210 : L < ((Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1)).image (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card)
    (h211 : 2 * K * L < ((Finset.range (R2 + 1) ×ˢ Finset.range (S2 + 1) ×ˢ Finset.range (T2 + 1)).image (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card)
    (h212 : K ^ 2 < (R2 + 1) * (S2 + 1) * (T2 + 1))
    (h213 : 3 * K ^ 2 * L < (R3 + 1) * (S3 + 1) * (T3 + 1))
    (h214 : ¬ (b1 ≤ max R1 R2 ∧ b2 ≤ max S1 S2 ∧ b3 ≤ max T1 T2))
    (h215 : ¬ (∃ u1 u2 u3 : ℤ, u1 * (b1 : ℤ) + u2 * (b2 : ℤ) + u3 * (b3 : ℤ) = 0 ∧ Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (S1 : ℝ) T1) ∧
        (|u2| : ℝ) ≤ ((R1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) T1) ∧
        (|u3| : ℝ) ≤ ((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) S1))) :
    ∃ kml rst : Fin N → ℕ × ℕ × ℕ, BB6Kit.RowsOK K L N kml ∧ BB6Kit.ColsOK R S T N rst ∧
      BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst ≠ 0 := by
  sorry
end BB6Kit
