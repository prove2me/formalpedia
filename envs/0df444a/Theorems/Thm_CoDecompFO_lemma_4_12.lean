-- Prove2me | Theorems.Thm_CoDecompFO_lemma_4_12
-- name    : CoDecompFO.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:01.445208+00:00
-- url     : https://prove2.me/theorems/1295cdc2-0f82-46c4-bb41-e1dae65cbdb7
-- title:
--   Lemma 4.12 — the induced hypothesis of a global assignment is the limit of its projections
-- statement:
--   Let $\mathcal T$ be a tree co-decomposition and let $\beta:[k]\to\lim\mathcal T$ be an assignment, with projection $\beta_a$ to each bag or adhesion $G_a$. Then $(T,\{\beta_a[G_a]\},\{g^e_t\})$ is a co-decomposition of hypotheses: the assignments satisfy $\beta_e=g^e_t\circ\beta_t$, and each head of $\beta_t[G_t]$ maps into the head of $\beta_e[G_e]$. Its limit is the hypothesis induced by $\beta$:
--   $$
--   \mathrm{head}\big(\beta[\lim\mathcal T]\big)=\bigcap_{t}\mathrm{head}\big(\beta_t[G_t]\big)=\bigcap_{t}\mathrm{head}\big(\beta_t[G_t]\big)\cap\bigcap_{e}\mathrm{head}\big(\beta_e[G_e]\big).
--   $$
--
--   This makes an atomic statement about the exponentially large limit checkable from its shadows in the bags.
--
--   Differences from the source:
--   - encoding: a limit of a co-decomposition of hypotheses with head [ℓ] → the same statement on atom sets: a head on [k] is its set of atoms, and a limit of heads is an intersection; reason: the point set of each head is [k] with identity maps, so a limit of heads is determined by the atoms that hold in all of them
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma 4.12, p.11; Lemma 4.24, p.13

import Mathlib
import Definitions.Def_CoDecompFO_Lim
import Definitions.Def_CoDecompFO_AltSat

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Lemma 4.12** (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, p.11): "Let T be a tree
co-decomposition and let β : [ℓ] → limT be a global assignment. Write β_a for the projection of β to
G_a. Then the tuple T′ = (T,{β_a[G_a]},{g^e_t}) is a co-decomposition of hypotheses. Furthermore, the
limit of T′ is the hypothesis induced on the limit of T by β. That is, limT′ = β[limT]."

The first four clauses say `T′` is a co-decomposition of hypotheses: the assignments project along the
maps `g^e_t`, and the head of `β_t[G_t]` maps into the head of `β_e[G_e]`. The last two say the head of
`β[lim T]` is the limit of the heads: the atoms holding in all bags, equivalently in all bags and
adhesions.

**Formalization Note** The assignment `β` is the list `l`, and `k = ℓ`. A hypothesis with a given
underlying assignment is its set of atoms. -/
theorem lemma_4_12 {σ : Sig} (T : CoDecomp σ) {k : ℕ} (l : List T.Lim) (hl : l.length = k) :
    (∀ e, l.map (CoDecomp.Lim.edgeProj e) = (l.map fun x => x.val (T.ends e).1).map (T.gl e)) ∧
    (∀ e, l.map (CoDecomp.Lim.edgeProj e) = (l.map fun x => x.val (T.ends e).2).map (T.gr e)) ∧
    (∀ e, atomsOf σ k (l.map fun x => x.val (T.ends e).1) ⊆
      atomsOf σ k (l.map (CoDecomp.Lim.edgeProj e))) ∧
    (∀ e, atomsOf σ k (l.map fun x => x.val (T.ends e).2) ⊆
      atomsOf σ k (l.map (CoDecomp.Lim.edgeProj e))) ∧
    atomsOf σ k l = ⋂ t, atomsOf σ k (l.map fun x => x.val t) ∧
    atomsOf σ k l = (⋂ t, atomsOf σ k (l.map fun x => x.val t)) ∩
      ⋂ e, atomsOf σ k (l.map (CoDecomp.Lim.edgeProj e)) := by sorry

end CoDecompFO
