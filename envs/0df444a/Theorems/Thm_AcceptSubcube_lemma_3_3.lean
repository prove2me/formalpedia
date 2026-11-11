-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_3_3
-- name    : AcceptSubcube.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:20.2556+00:00
-- url     : https://prove2.me/theorems/6257b850-4cfe-434a-872f-bbaa3ee7ff8c
-- title:
--   Lemma 3.3 — recovery near every fixed cheap reference
-- statement:
--   Fix $\ell\ge2$ and let $\mathcal I$ be a complete $\ell$-CSP on $m$ variables whose predicates each reject at least one pattern, and $1\le b\le m^\ell$. Run the recovery procedure of pp.12–13 with any orientation rule having the guarantee of Lemma 3.2. Then:
--
--   1. for every possible drawn set $S$, the output list $\mathcal L$ has at most $\Sigma(m,v_\ell(8))$ members;
--   2. for every fixed assignment $\sigma$ of cost at most $b$,
--   $$\mathbb P_S\Big[\min_{\tau\in\mathcal L}\mathrm{dist}(\tau,\sigma)\le\min\{m,\lceil C_\ell b^{1/\ell}\rceil\}\Big]\ge\frac34,\qquad C_\ell=8(v_\ell(16)+\ell+1),$$
--   the probability being over the uniform choice of the $s$-set $S$;
--   3. if the orientation rule is itself polynomial-time, the map $(\mathcal I,b,S)\mapsto\mathcal L$ is computed by one polynomial-time machine (one polynomial for all $b$), so the exponent of the running time is uniform in $b$.
--
--   $\sigma$ is not an input of the procedure. The lemma produces, on a star where an optimum is cheap, a center close to that optimum.
--
--   Differences from the source:
--   - generalization: the canonical orientation O_T of Lemma 3.2 → every orientation rule with the guarantee of Lemma 3.2 (GoodOrient); reason: the canonical rule is one of them, so the statement specializes to the source
--   - reading: a randomized polynomial-time procedure → the paper's procedure as a deterministic map of the drawn s-set; probability = exact fraction of uniformly drawn s-sets; time = TM2 polynomial-time map (I, b, S) ↦ list for every polynomial-time rule; reason: the lemma names its procedure; exact uniform sampling is the paper's ideal model (p.28); σ is not an input of the map
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.3, p.13 (procedure pp.12–13)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_FK
import Definitions.Def_AcceptSubcube_GoodOrient
import Definitions.Def_AcceptSubcube_recoverSet
import Definitions.Def_AcceptSubcube_encInst

namespace AcceptSubcube

/-- **Lemma 3.3 (Recovery for every fixed cheap reference)**, for the paper's procedure.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.3, p.13: "Fix ℓ ≥ 2. For an integer
1 ≤ b ≤ m^ℓ, a randomized polynomial-time procedure on a complete ℓ-CSP with m variables, whose
predicates each reject at least one pattern, returns a list L of at most Σ(m, v_ℓ(8)) assignments
such that, for every fixed σ of cost at most b, P[min_{τ∈L} dist(τ, σ) ≤ min{m, ⌈C_ℓ b^{1/ℓ}⌉}] ≥ 3/4,
C_ℓ = 8(v_ℓ(16) + ℓ + 1). (3) The exponent of the running time is uniform in b, and σ is not given
to the procedure." The procedure is the one of pp.12–13 (`recoverSet`).

Three clauses, for every orientation rule with the guarantee of Lemma 3.2: (1) for every draw the
list has at most `Σ(m, v_ℓ(8))` members; (2) for every `σ` of cost `≤ b`, the fraction of the
uniformly drawn `s`-sets `S` whose list contains an assignment within `min{m, ⌈C_ℓ b^{1/ℓ}⌉}` of `σ`
is at least `3/4`; (3) if the rule is itself polynomial-time, the map `(I, b, S) ↦ list` is computed
by one polynomial-time machine (one polynomial for all `b`, the budget being a binary input).

**Formalization Note.** The randomness is the uniform draw of the `s`-set `S` (`draws`; no draw when
`m < ℓ`), and the probability is the exact fraction of draws (the paper's "ideal model with exact
uniform sampling", p.28). `σ` is not an input of `recoverSet`. Stated for every orientation rule
satisfying `GoodOrient` (the canonical one of Lemma 3.2 is one). The drawn set is passed to the
machine as a sorted list. -/
theorem lemma_3_3 (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (∀ orient : List ℕ × List (List Bool) → List (List Bool × ℕ), GoodOrient orient →
      ∀ I : GInst, I.IsComplete ℓ → I.RejectsSome → ∀ b : ℕ, 1 ≤ b → b ≤ I.n ^ ℓ →
        (∀ S ∈ draws ℓ I.n b, (recoverSet orient ℓ I S).card ≤ sigmaSum I.n (vl ℓ 8)) ∧
        ∀ σ : Fin I.n → Bool, cost I σ ≤ b →
          (3 : ℝ) / 4 ≤
            (((draws ℓ I.n b).filter (fun S =>
                ∃ τ ∈ recoverSet orient ℓ I S, hdist τ σ ≤ recRadius ℓ I.n b)).card : ℝ) /
              ((draws ℓ I.n b).card : ℝ)) ∧
    (∀ orient : List ℕ × List (List Bool) → List (List Bool × ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encTF encOrient orient) →
      ∃ f : GInst × ℕ × List ℕ → List (List Bool),
        Nonempty (Turing.TM2ComputableInPolyTime encRecIn encAssignList f) ∧
        ∀ I : GInst, I.IsComplete ℓ → I.RejectsSome → ∀ b : ℕ, 1 ≤ b → b ≤ I.n ^ ℓ →
          ∀ S ∈ draws ℓ I.n b,
            (f (I, b, S.sort (· ≤ ·))).Nodup ∧
            ∀ y : List Bool, y ∈ f (I, b, S.sort (· ≤ ·)) ↔
              ∃ τ ∈ recoverSet orient ℓ I S, y = List.ofFn τ) := by sorry

end AcceptSubcube
