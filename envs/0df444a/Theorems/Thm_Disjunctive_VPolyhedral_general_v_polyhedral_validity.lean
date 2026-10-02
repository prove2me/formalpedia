-- Prove2me | Theorems.Thm_Disjunctive_VPolyhedral_general_v_polyhedral_validity
-- name    : Disjunctive.VPolyhedral.general_v_polyhedral_validity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:07:19.043723+00:00
-- url     : https://prove2.me/theorems/2f6230b7-52b6-4e16-8ba5-c9cac895d4a6
-- title:
--   Theorem 12.4 — the general V-polyhedral validity condition
-- statement:
--   This is Theorem 12.4 of Balas's *Disjunctive Programming*: relaxing each disjunct's V-
--   polyhedral system to a containing polyhedron still yields a valid cut for the mixed-integer
--   feasible set.
--
--   For each $h \in Q$, let $\tilde P^h$ be any polyhedron with $P^h \subseteq \tilde P^h
--   \subseteq C(x^h)$ (the LP cone at $x^h$), with vertex/ray sets $\tilde V^h$, $\tilde R^h$. If
--   $(\alpha,\beta)$ satisfies $\alpha p \ge \beta$ for every $p \in \tilde V^h$ and $\alpha r \ge
--   0$ for every $r \in \tilde R^h$ (over every $h$), then $\alpha x \ge \beta$ is valid for $P_I$.
--
--   The book's proof: let $C := \mathrm{conv}(\bigcup_h \tilde V^h) + \mathrm{cone}(\bigcup_h
--   \tilde R^h)$. Any $(\alpha,\beta)$ solving (12.8) is valid for all of $C$ (Proposition 12.1's
--   generator-validity criterion, applied to the single combined system), and since $P_I \subseteq
--   C$, the cut cannot cut off any point of $P_I$.
--
--   **Formalization Note.** `hPI_sub : PI ⊆ CombinedC ...` is taken as a hypothesis directly,
--   matching the book's own proof, which treats $P_I \subseteq C$ as already established from the
--   surrounding containment chain $P^h \subseteq \tilde P^h \subseteq C(x^h)$ and $F \subseteq C$
--   (not re-derived inside this theorem's own statement). `CombinedC` is the single combined
--   polyhedron (convex hull of the *union* of all $\tilde V^h$, not a union of per-$h$ pieces),
--   matching how the proof explicitly constructs $C$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 206, Theorem 12.4

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

namespace Disjunctive.VPolyhedral

/-- Theorem 12.4 (Balas §12.2, p. 206): if `(α,β)` satisfies `αp≥β` for every `p ∈ Ṽ^h` and
`αr≥0` for every `r ∈ R̃^h`, `h ∈ Q` (eq. (12.8), for relaxations `P^h ⊆ P̃^h ⊆ C(x^h)`), and the
mixed-integer feasible set `P_I` is contained in the resulting combined polyhedron `C`, then
`αx≥β` is valid for `P_I`. -/
theorem general_v_polyhedral_validity {n : ℕ} {Q : Type*} (Vidx Ridx : Q → Type*)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (PI : Set (Fin n → ℝ))
    (hPI_sub : PI ⊆ CombinedC Vidx Ridx vpt rvec)
    (alpha : Fin n → ℝ) (beta : ℝ) (hvalid : IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta) :
    ∀ x ∈ PI, beta ≤ dotProduct alpha x := by sorry

end Disjunctive.VPolyhedral
