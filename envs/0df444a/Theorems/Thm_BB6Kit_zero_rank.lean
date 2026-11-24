-- Prove2me | Theorems.Thm_BB6Kit_zero_rank
-- name    : BB6Kit.zero_rank
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-24T06:17:47.518361+00:00
-- url     : https://prove2.me/theorems/d8324511-30fd-4053-b699-f25ecf6b506a
-- title:
--   Mignotte–Voutier zero estimate, rank form: the $N\times RST$ interpolation matrix has independent rows
-- statement:
--   The rank form of the zero estimate in the Mignotte–Voutier kit (Proposition 3.11, Gouillon's zero lemma, applied in Section 4).
--
--   **Theorem.** Assume the hypotheses of `BB6Kit.zero_lemma`:
--
--   - the real case, with $\alpha_j>1$ multiplicatively independent integers, $b_j>0$ coprime and $\Lambda\ne0$;
--   - $K\ge3$, $L\ge5$ and $N=K(K+1)L/2\le RST$;
--   - (2.7) and (2.9)–(2.13), with $\chi>0$;
--   - neither (2.14) nor (2.15) holds.
--
--   Consider the $N\times RST$ matrix with rows indexed by the triples $(k,m,\ell)$, $k+m\le K-1$, $\ell<L$, and columns by $(r,s,t)\in[0,R)\times[0,S)\times[0,T)$. Its entries are $$\tbinom{r b'_3+t b'_1}{k}\tbinom{s b''_3+t b''_2}{m}\alpha_1^{\ell r}\alpha_2^{\ell s}\alpha_3^{\ell t},$$ where $b'_1=b_1/\gcd(b_1,b_3)$, $b'_3=b_3/\gcd(b_1,b_3)$, $b''_2=b_2/\gcd(b_2,b_3)$ and $b''_3=b_3/\gcd(b_2,b_3)$. The theorem says the rows are linearly independent over $\mathbb R$.
--
--   In the source, a linear dependence among the rows gives a nonzero polynomial of the shape (3.16) that vanishes on $\Sigma_1+\Sigma_2+\Sigma_3$, contradicting Proposition 3.11. Conditions (2.9)–(2.13) give (3.17)–(3.19) through Lemmas 3.15, 3.17 and 3.21, unless (2.14) or (2.15) holds. `BB6Kit.zero_lemma` follows from this by elementary linear algebra: some $N$ columns form an invertible submatrix.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Proposition 3.11 (Gouillon, Lemma 3.12), Lemmas 3.15, 3.17, 3.21, and Section 4 (proof of Theorem 2.1, the rank statement for the matrix of (2.6) over all columns).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem zero_rank (K L R S T N b1 b2 b3 α1 α2 α3 R1 S1 T1 R2 S2 T2 R3 S3 T3 : ℕ) (χ : ℝ)
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
    LinearIndependent ℝ (fun p : BB6Kit.rowSet K L => fun q : (Finset.range R ×ˢ Finset.range S ×ˢ Finset.range T) =>
      (Nat.choose ((q : ℕ × ℕ × ℕ).1 * (b3 / Nat.gcd b1 b3) + (q : ℕ × ℕ × ℕ).2.2 * (b1 / Nat.gcd b1 b3)) (p : ℕ × ℕ × ℕ).1 : ℝ) *
      (Nat.choose ((q : ℕ × ℕ × ℕ).2.1 * (b3 / Nat.gcd b2 b3) + (q : ℕ × ℕ × ℕ).2.2 * (b2 / Nat.gcd b2 b3)) (p : ℕ × ℕ × ℕ).2.1 : ℝ) *
      (α1 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (q : ℕ × ℕ × ℕ).1) * (α2 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (q : ℕ × ℕ × ℕ).2.1) *
      (α3 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (q : ℕ × ℕ × ℕ).2.2)) := by
  sorry
end BB6Kit
