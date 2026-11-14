-- Prove2me | Theorems.Thm_DvorakNorin2018_haven_cloud_balanced_configuration
-- name    : DvorakNorin2018.haven_cloud_balanced_configuration
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T18:12:57.817267+00:00
-- url     : https://prove2.me/theorems/a623eb47-4366-4e94-bb29-c97bbc356084
-- title:
--   Lemma 7 core: a haven yields the large tame cloud and balanced separation
-- statement:
--   Let $G$ be a finite graph, let $a\ge1$, and suppose that every induced subgraph has a balanced separation of order at most $a$. Let $\beta$ be a haven of order $k>15a$. Then there is a lexicographically minimum deletion set $W$ of size $14a$, a vertex set $X$, and a tame $W$-cloud on $G-\beta(W)$, of congestion at most $\alpha=14|\beta(W)|/(7a)$ and total supply greater than $14|\beta(W)|$. The set $X$ consists exactly of its hungry or saturated vertices; all supply and incoming and outgoing flow vanish outside $X$. Moreover, $W\subseteq X$, $X\cap\beta(W)=\varnothing$, and $(X,W\cup\beta(W))$ is a separation of the induced graph on $X\cup\beta(W)$ with intersection $W$. There is a balanced three-part separation $L,S,R$ of this induced graph, with $|S|\le a$, satisfying $$|(L\cap W)\cup(S\cap X)|\le a.$$ Here balanced means $3|L|,3|R|\le2|X\cup\beta(W)|$. In full-side notation $A=L\cup S$, $B=R\cup S$, the last inequality is precisely $|A\cap(W\cup B)\cap X|\le a$. This is the haven-based core of Dvorak--Norin Lemma 7, after obtaining the haven; the treewidth-to-haven duality is a separate dependency and is not asserted here.
-- source:
--   Dvorak and Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Lemma 7(a),(b) and its proof, PDF pp. 6-7. Formalization starts from the haven obtained in the first sentence, and uses ambient zero-extension of the cloud.

import Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
set_option autoImplicit false
open scoped Classical BigOperators
open TreewidthApprox.Pushed StableMSR.Recovery StableMSR.Recovery.Havens

namespace DvorakNorin2018
theorem haven_cloud_balanced_configuration {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (ha : 1 ≤ a) (hk : 15*a < k) :
    ∃ (W X : Finset V) (p : TameCloud.Data V), IsMinimumCut β (14*a) W ∧
      W.card = 14*a ∧ W ⊆ X ∧ Disjoint X (β W) ∧ X = activeVertices W p ∧
      X ∩ (W ∪ β W) = W ∧ (W ∪ β W) \ W = β W ∧
      IsPartition3 (X ∪ β W) (X \ W) W (β W) ∧ NoEdge G (X \ W) (β W) ∧
      TameCloud.Cloud (outsideGraph G (β W)) W (14*(β W).card/(7*(a : ℝ))) p ∧
      TameCloud.Tame W (14*(β W).card/(7*(a : ℝ))) p ∧
      14*((β W).card : ℝ) < TameCloud.total p ∧
      (∀ v ∉ X, p.1 v = 0 ∧ (∀ u, p.2 (u,v) = 0) ∧ ∀ u, p.2 (v,u) = 0) ∧
      ∃ L S R : Finset V, IsPartition3 (X ∪ β W) L S R ∧ NoEdge G L R ∧
        S.card ≤ a ∧ 3*L.card ≤ 2*(X ∪ β W).card ∧
        3*R.card ≤ 2*(X ∪ β W).card ∧ ((L ∩ W) ∪ (S ∩ X)).card ≤ a := by sorry
end DvorakNorin2018
