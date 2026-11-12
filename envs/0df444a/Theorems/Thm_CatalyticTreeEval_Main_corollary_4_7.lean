-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_corollary_4_7
-- name    : CatalyticTreeEval.Main.corollary_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:47.141526+00:00
-- url     : https://prove2.me/theorems/97b0dca7-efc5-41e3-8c46-b6fca711f472
-- title:
--   Corollary 4.7 — parameterized catalytic tree evaluation
-- statement:
--   For every real $\epsilon>0$ there are one finite deterministic binary machine, positive constants $C_s,C_c,C_t$ and a positive integer $q$, chosen before every height $h>0$, label length $\ell>0$, unrestricted TreeEval instance and initial tape. The same run outputs all $\ell$ bits of the root, restores the arbitrary catalyst exactly, and satisfies
--
--   $$\mathrm{free}\le\lceil C_s(\ell+h)\rceil,\qquad\mathrm{catalytic}\le\left\lceil2^{C_c\ell^\epsilon}\right\rceil,\qquad\mathrm{time}\le C_t2^{q(\ell+h)}.$$
--
--   The machine and constants may depend only on $\epsilon$. Every arbitrary tape at least as long as the bound is covered and its addressed prefix stays within that bound. No family construction, decoder or efficient evaluator is assumed. This is the full parameterized result from which the headline input-length bound follows.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: exp(O(ℓ^ε)) catalytic space and poly(2^(ℓ+h)) time → base-two exponential bounds with explicit positive constants, a fixed positive integer exponent and prefix-bounded arbitrary-bit runs; reason: fixes asymptotic quantifiers and rounding without changing the ε-family or excluding small positive inputs
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Corollary 4.7, printed p. 26 (PDF p. 28); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Resources

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Corollary 4.7, printed p.26 / PDF p.28. No efficient ingredient is a hypothesis. -/
theorem corollary_4_7 :
    ∀ ε : ℝ, 0 < ε →
    ∃ (M : Machine) (Cs Cc Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < q ∧
      ∀ (h l : ℕ), 0 < h → 0 < l → ∀ I : Tree l h,
      ComputesPrefix M I.encode (bits l I.value.val)
        (Cs * (l + h : ℝ)) (exp₂ (Cc * (l : ℝ) ^ ε))
        (Ct * (2 : ℝ) ^ (q * (l + h))) := by sorry

end CatalyticTreeEval.Main
