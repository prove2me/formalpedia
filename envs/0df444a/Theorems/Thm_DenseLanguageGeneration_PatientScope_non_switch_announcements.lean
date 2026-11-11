-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_non_switch_announcements
-- name    : DenseLanguageGeneration.PatientScope.non_switch_announcements
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:49:18.652814+00:00
-- url     : https://prove2.me/theorems/8266705b-99a1-4351-b424-80a19fec3f86
-- title:
--   Fact 3.13 — both non-switch announcement clauses
-- statement:
--   Let $\mathcal L$ be any indexed family of infinite positive-integer languages, $K=L_{i_\star}$ any target, and $a$ any injective full enumeration of $K$. In any paper round $t\ge2$, suppose the adversary's input $a_t$ has never been announced by either party and is not a switch loss. Then both
--
--   $$
--   a_t\in F_{t-1},\qquad b_{t-1}\le a_t,
--   $$
--
--   where $F_{t-1}$ is the previous end-of-round focus and $b_{t-1}$ the previous response of patient-scope. Whenever both integers belong to $K$, their target ranks satisfy
--
--   $$
--   r_K(b_{t-1})\le r_K(a_t).
--   $$
--
--   This is the non-switch counterpart of the charging lemma. The ambient comparison remains meaningful on early rounds outside $K$; on the settled tail the rank comparison is exactly the source's relabeled inequality. The previous response exists because $t\ge2$.
--
--   Differences from the source:
--   - encoding: positive family indices and rounds → family index i means source index i+1; stream index t means round t+1; history at completed time t has t inputs; reason: bijections preserve the countable family and every legal causal run, including the initial time zero
--   - encoding: comparison of integers, stated following the partial rank relabeling of K → both original membership and ambient order comparison, with the same comparison of ranks whenever both integers lie in K; reason: the rank map is increasing on K and undefined outside it; this spells out the source comparison without assigning a false rank to an invalid early response
-- source:
--   Cai, Li, Shen, Wang and Zhang, STOC 2027 submission #335 (October 2026), Fact 3.13, printed p.15 (PDF p.17); analogous proof of Fact 3.11, printed p.12 (PDF p.14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_density

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy

namespace DenseLanguageGeneration.PatientScope

/-- Cai et al., STOC 2027 submission #335 (October 2026), Fact 3.13,
printed p.15 (PDF p.17). Stream index t+1 has a previous response at index t.
State time t+1 is the end of that previous round. The ambient comparison remains
meaningful even for early outputs outside K. On the settled tail, both members
of K have their one-based rank comparison explicitly as well. -/
theorem non_switch_announcements (L : Family) (i : ℕ) (a : ℕ → ℕ+)
    (ha : IsEnumeration (L i) a) (t : ℕ)
    (hnew : UnannouncedInput (generator L) a (t + 1))
    (hns : ¬ SwitchLoss L a (t + 1)) :
    a (t + 1) ∈ focusAt L a (t + 1) ∧
    outputAt (generator L) a t ≤ a (t + 1) ∧
    (∀ (hb : outputAt (generator L) a t ∈ (L i).val)
       (hx : a (t + 1) ∈ (L i).val),
      rank (L i) ⟨outputAt (generator L) a t, hb⟩ ≤
        rank (L i) ⟨a (t + 1), hx⟩) := by sorry

end DenseLanguageGeneration.PatientScope
