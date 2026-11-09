-- Prove2me | Theorems.Thm_DerandLDT_corollary_6_1
-- name    : DerandLDT.corollary_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:04.88793+00:00
-- url     : https://prove2.me/theorems/143f93a0-b9ab-44dd-8f6d-831ff963eed8
-- title:
--   Corollary 6.1 — good points and good lines of the incidence graph
-- statement:
--   Let $\mathbb F$ be a finite field of size $q$, $U$ a set of $r$ distinct directions in $\mathbb F^2$, $\mathcal L$ the set of the $rq$ lines along $U$, $f : \mathbb F^2 \to \mathbb F$, and fix a degree-$k$ line table $(p_L)_L$. The points-vs-lines graph $G_f$ has the $q^2$ points and the lines of $\mathcal L$ as vertices and an edge $(a, L)$ when $a \in L$ and $p_L(a) = f(a)$. If $\varepsilon > 0$ and the local agreement of the table along $U$ is at least $\varepsilon$, then there are a set $P'$ of points and a set $\mathcal L' \subseteq \mathcal L$ of lines with
--
--   1. $|P'| \ge \frac{4\varepsilon}{5} q^2$ and $|\mathcal L'| \ge \frac{4\varepsilon}{5} qr$;
--   2. every point of $P'$ is adjacent in $G_f$ to at least $\varepsilon r/10$ lines of $\mathcal L'$;
--   3. every line of $\mathcal L'$ is adjacent in $G_f$ to at least $\varepsilon q/10$ points of $P'$.
--
--   The points of $P'$ and the lines of $\mathcal L'$ are the "good" points and lines on which the interpolation step (Lemma 6.2) and the proof of Theorem 1.2 work.
--
--   **Formalization Note** The local agreement is `DerandLDT.localAgr`; edges are `LineVsPoint.Accepted f P a L`.
--
--   Differences from the source:
--   - reading: "such that E_{ℓ∈𝓛}[agree(f|ℓ, P_{k,1})]." (the inequality is missing in print) → ε ≤ localAgr f P U; reason: the preceding sentence uses "the test passes with probability ε"
--   - generalization: G_f built from best-fit line polynomials → any degree-k line table P; reason: the best-fit table is one instance, and the argument does not use optimality
--   - encoding: a direction is a nonzero vector up to scalar multiples (u_i, u_j not scalar multiples) → a one-dimensional subspace of F² (finrank 1); r distinct directions = a Finset of r such subspaces; reason: the same object; proportional vectors give one subspace
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Corollary 6.1, p.25

import Definitions.Def_DerandLDT_localAgr

set_option autoImplicit false

universe u

namespace DerandLDT

open Classical in
/-- **Corollary 6.1** (good points and good lines). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point low-degree test*,
STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Corollary 6.1, p.25: *Let
`f : F² → F` be a function such that `E_{ℓ∈𝓛}[agree(f|ℓ, P_{k,1})] ≥ ε`. Then there is a
subgraph `G′_f = (P′, 𝓛′, E′)` of the points-vs-lines graph `G_f` with `|P′| ≥ (4ε/5)q²`,
`|𝓛′| ≥ (4ε/5)qr`, every vertex of `P′` of degree at least `εr/10` and every vertex of `𝓛′` of
degree at least `εq/10`.*

**Formalization Note.** `G_f` has the points of `F²` and the lines along `U` as vertices and an
edge `(a, L)` when the test accepts (`LineVsPoint.Accepted f P a L`: `a ∈ L` and the line
polynomial `p_L` agrees with `f` at `a`). The printed hypothesis is truncated; it is read as
`E_ℓ[agree(f|ℓ, P_{k,1})] ≥ ε`, here `ε ≤ localAgr f P U`, the value the preceding sentence
uses. The statement holds for every line table `P`, not only for a best-fit one. `G′_f` is
induced on `P′ ∪ 𝓛′`; `q = |F|` and `r = |U|`. -/
theorem corollary_6_1 (F : Type u) [Field F] [Fintype F] (k : ℕ)
    (U : Finset (Submodule F (Fin 2 → F))) (hU : ∀ u ∈ U, Module.finrank F u = 1)
    (f : (Fin 2 → F) → F) (P : LineVsPoint.LineTable F 2 k) (ε : ℝ) (hε : 0 < ε)
    (hagr : ε ≤ localAgr f P U) :
    ∃ (P' : Finset (Fin 2 → F)) (L' : Finset (LineVsPoint.Line F 2)), L' ⊆ linesAlong U ∧
      4 * ε / 5 * (Fintype.card F : ℝ) ^ 2 ≤ P'.card ∧
      4 * ε / 5 * ((Fintype.card F : ℝ) * U.card) ≤ L'.card ∧
      (∀ a ∈ P', ε * U.card / 10 ≤
        ((L'.filter fun L => LineVsPoint.Accepted f P a L).card : ℝ)) ∧
      (∀ L ∈ L', ε * Fintype.card F / 10 ≤
        ((P'.filter fun a => LineVsPoint.Accepted f P a L).card : ℝ)) := by sorry

end DerandLDT
