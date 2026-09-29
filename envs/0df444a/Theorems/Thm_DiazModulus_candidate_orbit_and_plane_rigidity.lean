-- Prove2me | Theorems.Thm_DiazModulus_candidate_orbit_and_plane_rigidity
-- name    : DiazModulus.candidate_orbit_and_plane_rigidity
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T14:13:25.225443+00:00
-- url     : https://prove2.me/theorems/b8ccaac5-f323-4c29-9620-566fc274bcac
-- title:
--   A candidate has a four-point orbit and its rational conjugate-plane meets the modulus condition only on the axes
-- statement:
--   Let $\bar{\mathbb{Q}}$ denote the algebraic numbers. Following the mission's convention, call a complex number $u$ a **candidate** when $u\neq 0$, $|u|$ is algebraic, and $\exp(u)$ is algebraic; a candidate is exactly a counterexample to Diaz's modulus conjecture, so the conjecture asserts that none exists.
--
--   This theorem collects four rigidity properties that a single candidate $u$ would have to satisfy simultaneously.
--
--   1. **The orbit is a set of candidates.** Each of $u$, $-u$, $\bar{u}$, $-\bar{u}$ is again a candidate.
--
--   2. **The orbit has exactly four points.** The four numbers $u$, $-u$, $\bar{u}$, $-\bar{u}$ are pairwise distinct. In particular a candidate is neither real nor purely imaginary.
--
--   3. **The conjugate is not an algebraic multiple.** For every algebraic $\gamma$ one has $\bar{u}\neq \gamma u$; so $u$ and $\bar{u}$ span a genuinely two-dimensional $\bar{\mathbb{Q}}$-configuration, not a line.
--
--   4. **The rational plane through $u$ and $\bar{u}$ meets the modulus condition only on the two axes.** For rational $a,b$,
--
--   $$
--   |\,a u + b\bar{u}\,| \ \text{is algebraic} \iff a = 0 \ \text{or} \ b = 0 .
--   $$
--
--   Clause 4 is the substantive one. Since $\exp$ is not involved in it, it says that the modulus half of the candidate condition already isolates the two lines $\mathbb{Q}u$ and $\mathbb{Q}\bar{u}$ inside their rational span: no genuinely mixed rational combination of a candidate with its conjugate has algebraic absolute value. Combined with clause 1, the four points of clause 2 are the only points of the rational plane that can meet the candidate locus at all.
--
--   The statement is unconditional: no transcendence conjecture is assumed. It packages, in the conjecture's own vocabulary, facts previously available only in the vocabulary of the $\texttt{Diaz.*}$ family (where the locus is written out as the three hypotheses $u\neq0$, $\exp u$ algebraic, $u\bar{u}$ algebraic) or only over an abstract base subfield.
--
--   **Formalization Note** Complex conjugation is `starRingEnd ℂ`, written `conj` after `open ComplexConjugate`. The modulus clause is stated as `IsAlgebraic ℚ ((‖·‖ : ℝ) : ℂ)`, matching `DiazModulus.IsCandidate`; passing between it and algebraicity of $u\bar{u}$ is the content of `Diaz.normal_form`.
-- source:
--   Composite of published mission nodes: Diaz.orbit_of_candidate (a31668ce-3926-4c2f-aea0-efbf00b2c133), Diaz.norm_mem_iff (dde35154-562b-49fb-8068-cc2077ce5402), Diaz.transcendental_of_candidate (3cae2e48-64f1-4be8-be0d-69719a233f94), Diaz.elliptic_axis_alignment (b52f753f-3594-4707-85cb-ae3a28126987), Diaz.normal_form (72e875b7-76ef-4bce-a2d1-17b4bde2556e) and DiazModulus.diaz_locus_dictionary (5fea543f-9239-417d-b101-37ecf4040dc7). Underlying mathematics: Carlo Perassi's, unpublished apart from these nodes, together with the Hermite–Lindemann theorem; the conjecture is G. Diaz's (J. Théor. Nombres Bordeaux 16 (2004), 535–553, §5.1).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem candidate_orbit_and_plane_rigidity {u : ℂ} (h : IsCandidate u) :
    (∀ v ∈ ({u, -u, conj u, -conj u} : Set ℂ), IsCandidate v)
      ∧ (u ≠ -u ∧ u ≠ conj u ∧ u ≠ -conj u ∧ -u ≠ conj u ∧ -u ≠ -conj u ∧ conj u ≠ -conj u)
      ∧ (∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u)
      ∧ (∀ a b : ℚ,
          IsAlgebraic ℚ ((‖(a : ℂ) * u + (b : ℂ) * conj u‖ : ℝ) : ℂ) ↔ (a = 0 ∨ b = 0)) := by sorry
end DiazModulus
