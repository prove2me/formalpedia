-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_2_4
-- name    : AcceptSubcube.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:38.906006+00:00
-- url     : https://prove2.me/theorems/4e539868-4550-478f-82a9-05fca6bdb6f1
-- title:
--   Lemma 2.4 — star validity and the incidence identity
-- statement:
--   Let $k\ge2$, $0\le t\le k-1$, and let $\mathcal I$ be a complete Boolean $k$-CSP on $n\ge k$ variables with nontrivial predicates having $\mathsf P_t$. Put $\ell=k-t$, $a_t=\binom kt$ and $\Pi_t=\binom nt$. Then:
--
--   1. for every $S\in\binom{[n]}t$ and $a\in\{0,1\}^S$, the star $\mathcal I_{S,a}$ is a complete $\ell$-CSP whose predicates each reject at least one pattern;
--   2. for every assignment $x$ and every such $S$, $C_{\mathcal I_{S,x_S}}(x_{-S})=d_S(x)$;
--   3. for every assignment $x$,
--   $$\sum_{S\in\binom{[n]}t}d_S(x)=a_t\,C_{\mathcal I}(x);$$
--   4. every assignment $x$ has a $t$-set $S$ with $d_S(x)\le a_t C_{\mathcal I}(x)/\Pi_t$.
--
--   The lemma is what lets the algorithm pin $t$ variables without leaving the class of complete instances, and it locates a star on which a fixed optimum is cheap.
--
--   Differences from the source:
--   - reading: standing assumptions of §2 (k ≥ 2, complete, nontrivial predicates, n ≥ k) and 0 ≤ t ≤ k − 1 of Definition 2.1 → explicit hypotheses 2 ≤ k, t ≤ k − 1, IsComplete k, Nontrivial, k ≤ n; reason: the section states them once at p.9; n ≥ k makes Π_t ≥ 1 in clause 4
--   - encoding: I_{S,a} on [n]∖S, a ∈ {0,1}^S → an instance on n − t variables numbered increasingly, a given by its set of ones; reason: same instance up to renaming of variables
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 2.4, p.11

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_subcubeDim
import Definitions.Def_AcceptSubcube_star

namespace AcceptSubcube

/-- **Lemma 2.4 (Star validity and incidence).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 2.4, p.11: "Under P_t, each I_{S,a} is a
complete auxiliary Boolean ℓ-CSP whose predicates each reject at least one pattern, and for every
assignment x, C_{I_{S,x_S}}(x_{−S}) = d_S(x), Σ_{S∈([n] choose t)} d_S(x) = a_t C_I(x). (2)
Consequently every assignment x has a set S with d_S(x) ≤ a_t C_I(x)/Π_t."

Four conclusions: (1) every star is complete of arity `ℓ = k − t` and rejects a pattern on every
scope; (2) the cost identity; (3) the incidence identity with `a_t = (k choose t)`; (4) the averaging
consequence with `Π_t = (n choose t)`.

**Formalization Note.** Standing assumptions of §2 (p.9): `k ≥ 2`, a complete instance with
nontrivial predicates, and `n ≥ k`; `0 ≤ t ≤ k − 1` as in Definition 2.1. Stars are instances on the
`n − t` variables of `[n] ∖ S`, renumbered increasingly (`star`); the pattern `a = x_S` is the set
`onesOn S x` of its ones. -/
theorem lemma_2_4 (k t : ℕ) (hk : 2 ≤ k) (ht : t ≤ k - 1) (I : GInst) (hI : I.IsComplete k)
    (hnt : I.Nontrivial) (hn : k ≤ I.n) (hPt : InstPt t I) :
    (∀ S ∈ (Finset.range I.n).powersetCard t, ∀ A ⊆ S,
        (star I S A).IsComplete (k - t) ∧ (star I S A).RejectsSome) ∧
    (∀ x : Fin I.n → Bool, ∀ S ∈ (Finset.range I.n).powersetCard t,
        cost (star I S (onesOn S x)) (restrictTo I S x) = dS I S x) ∧
    (∀ x : Fin I.n → Bool,
        ∑ S ∈ (Finset.range I.n).powersetCard t, dS I S x = k.choose t * cost I x) ∧
    (∀ x : Fin I.n → Bool, ∃ S ∈ (Finset.range I.n).powersetCard t,
        (dS I S x : ℝ) ≤ (k.choose t : ℝ) * (cost I x : ℝ) / (I.n.choose t : ℝ)) := by sorry

end AcceptSubcube
