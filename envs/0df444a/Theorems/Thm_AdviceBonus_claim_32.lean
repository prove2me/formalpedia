-- Prove2me | Theorems.Thm_AdviceBonus_claim_32
-- name    : AdviceBonus.claim_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:11.855059+00:00
-- url     : https://prove2.me/theorems/f2a86680-bb62-4f56-9b75-665cf7c07aea
-- title:
--   Claim (32) — at a symmetric scheme with $0<b<w$, sales stay constant iff $df_n=-\tfrac12db_n$; $S^f=2S^b$ (34)
-- statement:
--   Let the posterior distribution satisfy the standing assumptions, let $w>0$, and consider the symmetric compensation $(f_A,b_A)=(f_B,b_B)=(f,b)$ with $0<b<w$. For each firm $n\in\{A,B\}$, the expected sales $S_n$ have partial derivatives $S^f_n$ and $S^b_n$ with respect to the firm's own commission $f_n$ and own bonus $b_n$ (the rival's scheme held at $(f,b)$), and
--   $$
--   S^f_n=2S^b_n \qquad(34)
--   $$
--   and, for all marginal adjustments $(df_n,db_n)\in\mathbb R^2$,
--   $$
--   S^f_n\,df_n+S^b_n\,db_n=0\iff df_n=-\tfrac12\,db_n. \qquad(32)
--   $$
--
--   Along the direction $df_n=-\frac12db_n$ the firm keeps its sales constant while shifting pay from commission to bonus; the first-order condition (35) for the bonus is taken along it.
--
--   Differences from the source:
--   - encoding: dS_n = 0 → S^f_n df_n + S^b_n db_n = 0 with S^f_n, S^b_n the partial derivatives (HasDerivAt) in the firm's own instruments; reason: the total differential of S_n in (df_n, db_n), as in (9)
--   - reading: q̄1 by (4), no corner convention → clamped to [0, 1]; reason: the convention of footnote 19 for (2) and (3); at the symmetric scheme q̄1 = 1/2 is interior
--   - reading: density g > 0 on [0, 1], hazard rate increasing on [0, 1] → g continuous and positive on [0, 1], hazard rate weakly increasing on [0, 1); reason: the proofs use continuity (intermediate value theorem, p.35) and the hazard rate is undefined at q = 1
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), Appendix A, proof of Lemma 2, Claim (32), p.32, with eq. (34), p.33

import Mathlib
import Definitions.Def_AdviceBonus_Model

namespace AdviceBonus

/-- **Claim (32)** in the proof of Lemma 2, pp.32–34, with (34), p.33 (Honda–Inderst–Ottaviani,
SSRN 4125013, May 2022). At a symmetric scheme `(f_A, b_A) = (f_B, b_B) = (f, b)` with
`0 < b < w`, each firm's expected sales have partial derivatives `S^f_n`, `S^b_n` in its own
commission and bonus, `S^f_n = 2 S^b_n` (34), and a marginal adjustment keeps sales constant,
`S^f_n df_n + S^b_n db_n = 0`, iff `df_n = −db_n/2`. -/
theorem claim_32 (D : Dist) (w : ℝ) (hw : 0 < w) (f b : ℝ) (hb : 0 < b) (hbw : b < w) :
    (∃ Sf Sb : ℝ,
      HasDerivAt (fun x => salesA D w (x, b) (f, b)) Sf f ∧
      HasDerivAt (fun y => salesA D w (f, y) (f, b)) Sb b ∧
      Sf = 2 * Sb ∧
      ∀ df db : ℝ, Sf * df + Sb * db = 0 ↔ df = -(1 / 2) * db) ∧
    (∃ Sf Sb : ℝ,
      HasDerivAt (fun x => salesB D w (f, b) (x, b)) Sf f ∧
      HasDerivAt (fun y => salesB D w (f, b) (f, y)) Sb b ∧
      Sf = 2 * Sb ∧
      ∀ df db : ℝ, Sf * df + Sb * db = 0 ↔ df = -(1 / 2) * db) := by sorry

end AdviceBonus
