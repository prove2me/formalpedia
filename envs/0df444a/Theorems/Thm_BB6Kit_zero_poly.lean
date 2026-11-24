-- Prove2me | Theorems.Thm_BB6Kit_zero_poly
-- name    : BB6Kit.zero_poly
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-24T08:00:13.279798+00:00
-- url     : https://prove2.me/theorems/f85a0b7b-0b6b-4069-8637-0b951cdab08c
-- title:
--   Kit §4: no nonzero polynomial of degree $(K-1,L-1)$ vanishes on the image of the box
-- statement:
--   The polynomial form of the zero estimate step in Section 4 of the Mignotte–Voutier kit.
--
--   **Theorem.** Assume the hypotheses of `BB6Kit.zero_rank`. Let $\beta_1=b'_1/b'_3=b_1/b_3$ and $\beta_2=b''_2/b''_3=b_2/b_3$, and let $c_{a,b,e}$ be real numbers indexed by the triples $(a,b,e)$ with $a+b\le K-1$, $e\le L-1$. Suppose $$P(r+t\beta_1,\;s+t\beta_2,\;\alpha_1^r\alpha_2^s\alpha_3^t)=0,\qquad P(X_1,X_2,Y)=\sum c_{a,b,e}X_1^aX_2^bY^e,$$ for all integers $0\le r<R$, $0\le s<S$, $0\le t<T$. Then all the $c_{a,b,e}$ vanish.
--
--   In other words, no nonzero polynomial of total degree $\le K-1$ in $(X_1,X_2)$ and degree $\le L-1$ in $Y$ vanishes on the image of the box. In Section 4 of the source, this follows from Proposition 3.11 (Gouillon's zero estimate): $\Sigma_1+\Sigma_2+\Sigma_3$ lies in the box by (2.7), and (2.9)–(2.15) give (3.17)–(3.19) via Lemmas 3.15, 3.17 and 3.21. `BB6Kit.zero_rank` follows from this statement by writing $\binom{b'_3X_1}{k}\binom{b''_3X_2}{m}Y^\ell$ in the monomial basis.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Section 4 (proof of Theorem 2.1), with Proposition 3.11 and Lemmas 3.15, 3.17, 3.21.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem zero_poly (K L R S T N b1 b2 b3 α1 α2 α3 R1 S1 T1 R2 S2 T2 R3 S3 T3 : ℕ) (χ : ℝ)
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
    ∀ c : ℕ × ℕ × ℕ → ℝ,
      (∀ r < R, ∀ s < S, ∀ t < T,
        ∑ q ∈ BB6Kit.rowSet K L, c q * ((r : ℝ) + t * (((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ))) ^ q.1 * ((s : ℝ) + t * (((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ))) ^ q.2.1 *
          ((α1 : ℝ) ^ r * (α2 : ℝ) ^ s * (α3 : ℝ) ^ t) ^ q.2.2 = 0) →
      ∀ q ∈ BB6Kit.rowSet K L, c q = 0 := by
  sorry
end BB6Kit
