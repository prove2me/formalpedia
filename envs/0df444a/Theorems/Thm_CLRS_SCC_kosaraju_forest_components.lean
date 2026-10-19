-- Prove2me | Theorems.Thm_CLRS_SCC_kosaraju_forest_components
-- name    : CLRS.SCC.kosaraju_forest_components
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T03:00:31.599059+00:00
-- url     : https://prove2.me/theorems/4db6f882-a5d2-4623-802d-e249e5f42f70
-- title:
--   Kosaraju: the second DFS forest identifies mutual reachability
-- statement:
--   Let $G$ be a finite directed multigraph and let $T$ be a transpose of $G$, retaining vertex count and reversing every adjacency occurrence with its multiplicity. Suppose a first DFS forest on $G$ satisfies the stated parent, event-time, white-path, component-tree and finish-order properties. Suppose a second DFS forest on $T$ satisfies the same forest contract, and its outer-loop input order is the reverse of the first forest's increasing finish order.
--
--   Then for every pair of vertices $u,v$ of $G$,
--   $$c_2(u)=c_2(v)\quad\Longleftrightarrow\quad u\leadsto_G v\ \text{ and }\ v\leadsto_G u.$$
--   Here $c_2$ is the second forest's tree label and reachability allows zero-edge walks. Thus each second-pass predecessor tree is exactly one strongly connected component of the original graph. The assertion includes empty graphs, self-loops and parallel arcs; labels are not canonical. All execution, heap-allocation and cost questions are separated from this purely mathematical two-forest lemma.
-- source:
--   Cormen, Leiserson, Rivest and Stein, Introduction to Algorithms, fourth edition (MIT Press, 2022), §20.5, Theorem 20.16 (correctness of STRONGLY-CONNECTED-COMPONENTS), with the finish-time argument of Lemma 20.14. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ . Supporting primary-source lecture presentation: John Fawcett, Cambridge Algorithms 2, Lent 2025/26, slides 58–60 and 67, https://www.cl.cam.ac.uk/teaching/2526/Algorithm2/Algorithms2-v1.2.pdf .

import Definitions.Def_CLRS_DFS_Program
set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS

theorem CLRS.SCC.kosaraju_forest_components
    (g t : Graph) (transposed : IsTranspose g t)
    (q₁ p₁ d₁ f₁ o₁ c₁ q₂ p₂ d₂ f₂ o₂ c₂ : Seq) (k₁ k₂ : Nat)
    (first : Forest g q₁ p₁ d₁ f₁ o₁ c₁ k₁)
    (second : Forest t q₂ p₂ d₂ f₂ o₂ c₂ k₂)
    (reversed : ∀ i : Nat, i < g.size → q₂ (i : Int) = o₁ ((g.size : Int) - 1 - i)) :
    ∀ u v : Int, Vertex g u → Vertex g v →
      (c₂ u = c₂ v ↔ StronglyConnected g u v) := by sorry
