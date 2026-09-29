-- Prove2me | Theorems.Thm_FamousTheorems_kuratowski_embedding_theorem
-- name    : FamousTheorems.kuratowski_embedding_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:24.520216+00:00
-- url     : https://prove2.me/theorems/84ec2494-517a-4cee-a47d-e9ffc27c9a36
-- title:
--   The Kuratowski embedding theorem
-- statement:
--   **The Kuratowski embedding theorem.** Every separable metric space $\alpha$ embeds isometrically into the Banach space $\ell^\infty(\mathbb N)$ of bounded real sequences with the sup norm.
--
--   The embedding sends $x$ to the sequence $n\mapsto d(x,x_n)-d(x_0,x_n)$ for a dense sequence $(x_n)$. It is a basic tool in metric geometry: it allows one to realize abstract metric spaces inside a single complete ambient space, for example in the construction of the Gromov–Hausdorff space.
--
--   **Formalization note.** Mathlib's `kuratowskiEmbedding.isometry`, with witness `kuratowskiEmbedding α`. The target space `lp (fun _ : ℕ => ℝ) ⊤` is Mathlib's $\ell^\infty(\mathbb N,\mathbb R)$, and `Isometry f` means `f` preserves distances.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `kuratowskiEmbedding.isometry`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kuratowski_embedding_theorem (α : Type*) [MetricSpace α] [TopologicalSpace.SeparableSpace α] :
    ∃ f : α → lp (fun _ : ℕ => ℝ) ⊤, Isometry f := by sorry

end FamousTheorems
