-- Prove2me | Theorems.Thm_FamousTheorems_tarski_vaught_test
-- name    : FamousTheorems.tarski_vaught_test
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:09.524426+00:00
-- url     : https://prove2.me/theorems/c1988594-897a-440a-97b9-5aa8750797c3
-- title:
--   The Tarski–Vaught test
-- statement:
--   **The Tarski–Vaught test.** Let $f:M\to N$ be an embedding of $L$-structures. Suppose that for every formula $\varphi(\bar x,y)$ and every tuple $\bar a$ from $M$, whenever $N\models\varphi(f\bar a,b)$ for some $b\in N$, there is already some $c\in M$ with $N\models\varphi(f\bar a,f c)$. Then $f$ is elementary: for every formula $\varphi(\bar x)$ and every tuple $\bar a$ from $M$,
--   $$N\models\varphi(f\bar a)\iff M\models\varphi(\bar a).$$
--
--   This is the standard criterion for recognising elementary substructures. It is the key step in the downward Löwenheim–Skolem theorem, where one closes a subset under witnesses for existential formulas.
--
--   **Formalization note.** Mathlib's `FirstOrder.Language.Embedding.isElementary_of_exists`. Formulas with $n+1$ free variables are encoded as `L.BoundedFormula Empty (n + 1)`, and the tuple $(f\bar a, b)$ is `Fin.snoc (f ∘ x) b`. The conclusion is exactly the definition of an elementary embedding, spelled out.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FirstOrder.Language.Embedding.isElementary_of_exists`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tarski_vaught_test {L : FirstOrder.Language} {M N : Type*} [L.Structure M] [L.Structure N] (f : L.Embedding M N)
    (htv : ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) (a : N),
      φ.Realize default (Fin.snoc (f ∘ x) a : _ → N) →
        ∃ b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ → N)) :
    ∀ {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M), φ.Realize (f ∘ x) ↔ φ.Realize x := by sorry

end FamousTheorems
