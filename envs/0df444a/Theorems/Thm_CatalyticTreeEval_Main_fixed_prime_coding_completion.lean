-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_fixed_prime_coding_completion
-- name    : CatalyticTreeEval.Main.fixed_prime_coding_completion
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:20:52.995591+00:00
-- url     : https://prove2.me/theorems/92e4b060-4704-413e-b468-ea1c04a09f04
-- title:
--   Corollary 4.7 — fixed-prime frame and parameter-header construction
-- statement:
--   Fix distinct odd primes $p_1,\ldots,p_t$ and positive charged-printer constants. Suppose Corollary 3.11 supplies size-$2^\ell$ canonical-score matching families and a uniform vector printer, and Lemma 3.19 supplies a canonical-sumset decoder with sparsity at most $3^t$ and a charged term printer. Then these component interfaces can be packaged as one valid parameterized Section 4 frame, with adapted vector and decoder printers sharing one common access-space multiplier.
--
--   For every $\ell\ge1$, the frame indexed by `natCode` $\ell$ has the prescribed modulus, label length, common decoder sparsity, dimension bound, and access scale $s=O(\ell)$. The parameter strings satisfy the exponential length premise of Corollary 4.2. In addition, there is a fixed finite printer which, from the bare binary encoding of a tree instance, prints exactly the frame's self-delimiting parameter header, in workspace $O(s)$ and time $2^{O(s)}$. The explicit output and printer bounds are retained rather than treating parameter conversion as free.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533, proof of Corollary 4.7, printed pp. 26–27 (PDF pp. 28–29); Section 4 parameter/access interface, printed p. 21 (PDF p. 23); charged printer encoding in the mission's formalization of Remark 3.8, printed p. 16 (PDF p. 18).

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

/-- Uniform fixed-prime frames, adapted component printers, and a header printer. -/
theorem CatalyticTreeEval.Main.fixed_prime_coding_completion
    {t : ℕ} (p : Fin t → ℕ) (hp : OddPrimeData p)
    (MV MD : Machine) (Cd Cv Cs Ct : ℝ) (qd : ℕ)
    (hCd : 0 < Cd) (hCv : 0 < Cv) (hCs : 0 < Cs) (hCt : 0 < Ct) (hq : 0 < qd)
    (hvectors : ∀ l : ℕ, 1 ≤ l →
      ∃ (d : ℕ) (U V : Fin (2 ^ l) → Vec (modulus p) d),
        (d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
          (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ))) ∧
        SMatching (canonical p (modulus p)) U V ∧
        VectorAccess MV (natCode l) U V (Cv * (l + lg d + lg (modulus p))))
    (hdecoder : ∃ (k : ℕ) (D : Decoder (modulus p) k), k ≤ 3 ^ t ∧
      IsDecoder (sumset (canonical p (modulus p))) D ∧
      (∀ j z, PrintsIn MD (decoderRequest (primeCode p) j.val z.val)
        (decoderOutput D j z) (Cs * log₂ (modulus p))
        (Ct * (1 + log₂ (modulus p)) ^ qd))) :
    ∃ (F : List Bool → Frame) (domain : Set (List Bool))
      (MV' MD' MP : Machine) (A r k : ℕ) (Csl Ch Cht : ℝ),
      0 < A ∧ 0 < r ∧ 0 < Csl ∧ 0 < Ch ∧ 0 < Cht ∧
      (∀ a ∈ domain, (F a).valid ∧ a.length ≤ 2 ^ (A * (F a).s) ∧
        (F a).access a MV' MD' A) ∧
      (∀ l : ℕ, 1 ≤ l →
        natCode l ∈ domain ∧
        (F (natCode l)).m = modulus p ∧
        (F (natCode l)).l = l ∧
        (F (natCode l)).k = k ∧ k ≤ 3 ^ t ∧
        ((F (natCode l)).d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
          (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ))) ∧
        ((F (natCode l)).s : ℝ) ≤ Csl * l) ∧
      (∀ a ∈ domain, ∀ h : ℕ, 0 < h → ∀ I : Tree (F a).l h,
        PrintsIn MP I.encode (listCode ((F a).params a))
          (Ch * (F a).s) (Cht * ((2 : ℝ) ^ (F a).s + 1) ^ r)) := by sorry
