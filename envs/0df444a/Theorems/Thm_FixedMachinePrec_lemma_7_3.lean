-- Prove2me | Theorems.Thm_FixedMachinePrec_lemma_7_3
-- name    : FixedMachinePrec.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:10.402674+00:00
-- url     : https://prove2.me/theorems/6415bb90-ea3e-42d5-9248-51da9baa362d
-- title:
--   Lemma 7.3 — the prefix selected by a separator
-- statement:
--   Let $m\ge3$, let $\prec$ be a strict partial order on $J$, and let $(Z_1,\dots,Z_q)$ be a nonempty feasible full schedule of $U\subseteq J$ with local time $\tau_U$. Suppose the actual slot $z=Z_r$ separates the ideal $S$ on $U$, and $H\subseteq J$ satisfies $H\cap U=S$. Then:
--
--   1. $$\mathrm{Pref}_U(z)=\{x\in U:\tau_U(x)<r\}=U\cap B_z(H),\qquad B_z(H)=P_z\cup(H\setminus\hat D_z);$$
--   2. for the reversed precedence and the reversed schedule $(Z_q,\dots,Z_1)$, the same slot (at position $q+1-r$) separates $U\setminus S$;
--   3. if $H$ is a global ideal, then $B_z(H)$ is a global ideal.
--
--   This turns a temporal prefix into a global formula whose only local ingredient is a set agreeing with the cutoff on $U$.
--
--   Differences from the source:
--   - generalization: U the jobs of a nonempty contiguous interval of a complete feasible witness, with its local schedule → any nonempty feasible full schedule (Z_1, …, Z_q) of any U ⊆ J; reason: the local schedule of a contiguous interval is a feasible full schedule of U, so the source's case is an instance
--   - encoding: reversing time and precedence → the dual order fun x y => y ≺ x and the reversed slot list; reason: the reversed frame of §7.1, p.28
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Lemma 7.3, p.34

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator

namespace FixedMachinePrec

/-- **Lemma 7.3 (The prefix selected by a separator).** Jansen, *Precedence Constraint Scheduling on
a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Lemma 7.3, p.34: "Suppose that z is an
actual separator of S on U and H ⊆ J satisfies H ∩ U = S. Then Pref_U(z) = U ∩ B_z(H). Reversing
both time and precedence and replacing S by U \ S preserves separation. If, in addition, H is a
global ideal, then B_z(H) is a global ideal."

Let `Zs = (Z_1, …, Z_q)` be a nonempty feasible full schedule of `U`, let `z = Z_r` separate the
ideal `S` on `U`, and let `H ⊆ J` with `H ∩ U = S`. Then
1. `Pref_U(z) = {x ∈ U : τ_U(x) < r} = U ∩ B_z(H)`, where `B_z(H) = P_z ∪ (H \ D̂_z)`;
2. for the reversed precedence and the reversed schedule `(Z_q, …, Z_1)`, the same slot (now at
   position `q + 1 − r`) separates `U \ S`;
3. if `H` is a global ideal, so is `B_z(H)`.

**Formalization Note** §7.2 takes `U` to be a nonempty contiguous interval of a complete feasible
witness and `Zs` its local schedule; the lemma is stated for every nonempty feasible full schedule
`Zs` of `U`, which every such local schedule is. -/
theorem lemma_7_3 {N : ℕ} (m : ℕ) (hm : 3 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (U : Finset (Fin N)) (Zs : List (Finset (Fin N)))
    (hZs : IsFullSchedule prec m U Zs) (hne : Zs ≠ []) (S H : Finset (Fin N)) (r : ℕ)
    (hsep : Separates prec Zs S r) (hH : H ∩ U = S) :
    slotsBetween Zs 0 r = U ∩ sepFormula prec (Zs.getD (r - 1) ∅) H ∧
    Separates (fun x y => prec y x) Zs.reverse (U \ S) (Zs.length + 1 - r) ∧
    (IsIdealIn prec Finset.univ H →
      IsIdealIn prec Finset.univ (sepFormula prec (Zs.getD (r - 1) ∅) H)) := by sorry

end FixedMachinePrec
