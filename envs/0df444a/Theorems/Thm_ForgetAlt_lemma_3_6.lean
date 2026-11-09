-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_6
-- name    : ForgetAlt.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:56.02081+00:00
-- url     : https://prove2.me/theorems/d5888845-d6aa-408f-b819-20acfec3b433
-- title:
--   Lemma 3.6: properties (M1)–(M4) of minimum incoming edges
-- statement:
--   Let $T$ be any ABT with MIEs $e^*_T(\cdot)$ fixed arbitrarily, and let $t$ be a vertex with $\mathrm{dist}^\beta(t)<\infty$. Then:
--
--   1. **(M1)** every incoming edge $e$ of $T(t)$ with $e\notin E^+_H(t)$ and $\mathrm{vlevel}(e)\le\mathrm{vlevel}(t)$ has $\mathrm{hlevel}(e)<\mathrm{dist}^\beta(t)$;
--   2. **(M2)** $\mathrm{vlevel}(e^*_T(t))\le\mathrm{vlevel}(t)$;
--   3. **(M3)** for every non-tree edge $e'$ incident to $t$, $\mathrm{level}(e')>\mathrm{level}(e^*_T(t))$ unless $e'\notin E^+_H(t)$ and $\rho(e')=\alpha(t)$; and if $e'\notin E^+_H(t)$, $\rho(e')=\beta(t)$, then $\mathrm{vlevel}(e')>\mathrm{vlevel}(e^*_T(t))$;
--   4. **(M4)** no MIE of $T(t)$ lies in $E^+_H(t)$, and $\mathrm{hlevel}(e^*_T(t))<\mathrm{dist}^\beta(t)$.
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - encoding: the convention “whenever an incoming edge of T(t) is considered, we implicitly assume Ẽ_T(t) ≠ ∅” (p.19) → no such hypothesis; reason: under dist^β(t) < ∞ the paper proves Ẽ_T(t) ≠ ∅ (p.18), so e*_T(t) is an MIE without it
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.6, printed p.19 (PDF p.20)

import Mathlib
import Definitions.Def_ForgetAlt_ABT

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.6**, printed p.19 (PDF p.20). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Let `t ∈ V(T)` be a vertex with `dist^β(t) < ∞`. Then the following properties hold. (M1) Every
incoming edge `e` of `T(t)` with `e ∉ E⁺_H(t)` and `vlevel(e) ≤ vlevel(t)` satisfies
`hlevel(e) < dist^β(t)`. (M2) `vlevel(e*_T(t)) ≤ vlevel(t)`. (M3) Let `e′` be any non-tree edge
incident to `t`. Then `level(e′) > level(e*_T(t))` holds unless both `e′ ∉ E⁺_H(t)` and
`ρ(e′) = α(t)` are satisfied. In particular, if `e′ ∉ E⁺_H(t)` and `ρ(e′) = β(t)`, then
`vlevel(e′) > vlevel(e*_T(t))`. (M4) No MIE of `T(t)` belongs to `E⁺_H(t)`, and
`hlevel(e*_T(t)) < dist^β(t)` holds."

**Formalization Note.** `T` is any ABT `par` and `e*_T` any MIE choice `mie` (Section 3.3.1:
"`T` is any fixed ABT"). The convention "whenever an incoming edge of `T(t)` is considered,
we implicitly assume `Ẽ_T(t) ≠ ∅`" (p.19) is not a hypothesis: the paper proves `Ẽ_T(t) ≠ ∅`
whenever `dist^β(t) < ∞` (p.18), so `mie t` is an MIE of `T(t)` here. -/
theorem lemma_3_6 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (par : ExtV V → ExtV V) (hT : IsABT G M par) (mie : ExtV V → Sym2 (ExtV V))
    (hmie : MIEChoice G M par mie) (t : ExtV V) (ht : distB G M t < ⊤) :
    (∀ e, IsIncoming G M par t e → e ∉ EplusH G M t → vlevelE G M e ≤ vlevelV G M t →
      hlevelE G M e < distB G M t) ∧
    vlevelE G M (mie t) ≤ vlevelV G M t ∧
    (∀ e' ∈ (extGraph G M).edgeSet, t ∈ e' → ¬ IsTreeEdge G M par e' →
      (¬ (e' ∉ EplusH G M t ∧ rho G M e' = alpha G M t) → level G M (mie t) < level G M e') ∧
      (e' ∉ EplusH G M t → rho G M e' = beta G M t → vlevelE G M (mie t) < vlevelE G M e')) ∧
    (∀ e, IsMIE G M par t e → e ∉ EplusH G M t) ∧ hlevelE G M (mie t) < distB G M t := by sorry

end ForgetAlt
