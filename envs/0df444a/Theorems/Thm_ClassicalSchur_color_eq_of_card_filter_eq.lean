-- Prove2me | Theorems.Thm_ClassicalSchur_color_eq_of_card_filter_eq
-- name    : ClassicalSchur.color_eq_of_card_filter_eq
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:03.092477+00:00
-- url     : https://prove2.me/theorems/2c78868a-b993-4389-a94a-3ecd7c07f9d0
-- title:
--   Automorphism extension: an involution preserving the colours on $W$ and the colour degrees of $v$ preserves the colour of the pair with $e \notin W$
-- statement:
--   This is a general counting lemma for colourings of pairs: if an involution $J$ of a set $W$ keeps the colours of the pairs in $W$, and a point $v \in W$ and its image $J(v)$ have the same colour degrees in $W \cup \{e\}$, then the pairs $(v, e)$ and $(J(v), e)$ have the same colour.
--
--   Let $\alpha$ and $\gamma$ be types with decidable equality (points and colours), and let $\mathrm{col} : \alpha \to \alpha \to \gamma$ give each ordered pair $(x, y)$ a colour $\mathrm{col}(x, y)$. Let $W$ be a finite subset of $\alpha$, let $e \in \alpha$ with $e \notin W$, and let $J : \alpha \to \alpha$ satisfy, for all $x, y \in W$:
--
--   1. $J(x) \in W$;
--   2. $J(J(x)) = x$;
--   3. $\mathrm{col}(J(x), J(y)) = \mathrm{col}(x, y)$.
--
--   Let $v \in W$, and suppose that $v$ and $J(v)$ have the same number of neighbours of each colour in $W \cup \{e\}$: for every colour $i \in \gamma$,
--
--   $$
--   \bigl|\{\, w \in (W \cup \{e\}) \setminus \{v\} : \mathrm{col}(v, w) = i \,\}\bigr| = \bigl|\{\, w \in (W \cup \{e\}) \setminus \{J(v)\} : \mathrm{col}(J(v), w) = i \,\}\bigr| .
--   $$
--
--   Then
--
--   $$
--   \mathrm{col}(v, e) = \mathrm{col}(J(v), e) .
--   $$
--
--   In the mission the lemma is applied with $W$ the central neighbourhood without its endpoint, $e = 2m + 1$, $J(x) = 2m - x$ and $\mathrm{col}(x, y) = c(|x - y|)$; the saturation theorem supplies the equal colour degrees, and the conclusion is the forced reflection.
--
--   **Formalization Note.** The colour function takes ordered pairs and need not be symmetric; the degrees of $v$ and $J(v)$ are counted with $v$ and $J(v)$ as first argument, and the pair of a point with itself is not counted. The types $\alpha$ and $\gamma$ are arbitrary (Lean `Type*` with `DecidableEq`), and $W$ is a `Finset`. The conditions on $J$ are required only on $W$. The case $J(v) = v$ is allowed, and the conclusion is then immediate.
-- source:
--   A. McKenna, "S(6) ≤ 1801 if R₄(3) ≤ 61: a centred Schur bound and the structure at the frontier", Zenodo (2026), https://doi.org/10.5281/zenodo.23156099, Lemma 4.5 (§4.3, automorphism extension). Lean source: https://github.com/mysticflounder/schur-centred-bound/blob/v1.0.1/ClassicalSchur/Frontier.lean#L368-L411 (release v1.0.1, doi:10.5281/zenodo.23156444).

import Mathlib

open Finset

theorem ClassicalSchur.color_eq_of_card_filter_eq {α γ : Type*} [DecidableEq α] [DecidableEq γ]
    (col : α → α → γ) {W : Finset α} {e : α} (he : e ∉ W) (J : α → α)
    (hJ : ∀ x ∈ W, J x ∈ W) (hJJ : ∀ x ∈ W, J (J x) = x)
    (hcol : ∀ x ∈ W, ∀ y ∈ W, col (J x) (J y) = col x y) {v : α} (hv : v ∈ W)
    (hdeg : ∀ i, (((insert e W).erase v).filter fun w => col v w = i).card =
      (((insert e W).erase (J v)).filter fun w => col (J v) w = i).card) :
    col v e = col (J v) e := by sorry
